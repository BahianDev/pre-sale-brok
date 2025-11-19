use anchor_lang::prelude::*;
use anchor_lang::system_program::{self, Transfer as SystemTransfer};
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token::{self, Mint, Token, TokenAccount, Transfer};

declare_id!("7V8Dz33M4tV4uPw1egTYaDJEyTUupMFRqZKwfZcZaGgb");

// -----------------------------
// Constantes
// -----------------------------
const BPS_MAX: u16 = 10_000;
const WEEK_SECONDS: u64 = 120; // 7 dias em segundos
const RELEASE_PERCENTAGE: u16 = 750; // 7.5% em BPS

// -----------------------------
// Enums e Structs
// -----------------------------
#[derive(AnchorSerialize, AnchorDeserialize, Clone, PartialEq, Eq)]
pub enum Phase {
    Whitelist, // Phase 1: Preço 0.001 SOL
    Public,    // Phase 2: Preço 0.01 SOL
    Final,     // Phase 3: Preço 0.015 SOL
}

// -----------------------------
// Programa
// -----------------------------
#[program]
pub mod presale {
    use super::*;

    /// Inicializa a pre-sale com as fases
    pub fn initialize(ctx: Context<Initialize>, params: InitializeParams) -> Result<()> {
        let state = &mut ctx.accounts.state;
        let token_decimals = 1_000_000_000; // 9 decimais

        require!(params.start_ts < params.end_ts, PresaleError::InvalidTime);

        state.authority = ctx.accounts.authority.key();
        state.mint = ctx.accounts.mint.key();
        state.vault = ctx.accounts.vault.key();
        state.treasury = ctx.accounts.treasury.key();

        state.start_ts = params.start_ts;
        state.end_ts = params.end_ts;
        state.tge_ts = params.tge_ts;
        state.total_raised_lamports = 0;

        // Configuração das fases
        state.current_phase = Phase::Whitelist;

        // CORREÇÃO: tokens_per_sol já deve vir calculado com decimais
        state.phase1_tokens_per_sol = params.phase1_tokens_per_sol;
        state.phase2_tokens_per_sol = params.phase2_tokens_per_sol;
        state.phase3_tokens_per_sol = params.phase3_tokens_per_sol;

        // CORREÇÃO: Multiplica os limites oferecidos pelos decimais
        state.phase1_tokens_offered = params
            .phase1_tokens_offered
            .checked_mul(token_decimals)
            .ok_or(PresaleError::MathOverflow)?;
        state.phase2_tokens_offered = params
            .phase2_tokens_offered
            .checked_mul(token_decimals)
            .ok_or(PresaleError::MathOverflow)?;
        state.phase3_tokens_offered = params
            .phase3_tokens_offered
            .checked_mul(token_decimals)
            .ok_or(PresaleError::MathOverflow)?;

        state.phase1_sold_tokens = 0;
        state.phase2_sold_tokens = 0;
        state.phase3_sold_tokens = 0;
        state.finalized = false;

        // Verificações de vault
        require_keys_eq!(
            ctx.accounts.vault.mint,
            ctx.accounts.mint.key(),
            PresaleError::InvalidVaultMint
        );
        require_keys_eq!(
            ctx.accounts.vault.owner,
            state.key(),
            PresaleError::InvalidVaultOwner
        );

        Ok(())
    }

    /// Adiciona um comprador à whitelist
    pub fn whitelist_set(ctx: Context<WhitelistSet>) -> Result<()> {
        let state = &ctx.accounts.state;
        require!(
            state.authority == ctx.accounts.authority.key(),
            PresaleError::Unauthorized
        );
        require!(!state.finalized, PresaleError::AlreadyFinalized);

        let w = &mut ctx.accounts.whitelist;
        w.state = state.key();
        w.buyer = ctx.accounts.buyer.key();
        Ok(())
    }

    /// Avança para a próxima fase (somente autoridade)
    pub fn advance_phase(ctx: Context<AdvancePhase>) -> Result<()> {
        let state = &mut ctx.accounts.state;

        require!(!state.finalized, PresaleError::AlreadyFinalized);

        match state.current_phase {
            Phase::Whitelist => {
                state.current_phase = Phase::Public;
            }
            Phase::Public => {
                state.current_phase = Phase::Final;
            }
            Phase::Final => {
                return Err(PresaleError::AlreadyFinalPhase.into());
            }
        }

        Ok(())
    }

    pub fn buy(ctx: Context<Buy>, lamports: u64) -> Result<()> {
        let clock = Clock::get()?;
        let state = &mut ctx.accounts.state;

        require!(!state.finalized, PresaleError::AlreadyFinalized);
        require!(
            clock.unix_timestamp as u64 >= state.start_ts,
            PresaleError::SaleNotStarted
        );
        require!(
            clock.unix_timestamp as u64 <= state.end_ts,
            PresaleError::SaleEnded
        );

        // Atualiza buyer state
        let buyer_state = &mut ctx.accounts.buyer_state;
        if buyer_state.state == Pubkey::default() {
            buyer_state.state = state.key();
            buyer_state.buyer = ctx.accounts.buyer.key();
            buyer_state.contributed_lamports = 0;
            buyer_state.allocated_tokens = 0;
            buyer_state.claimed_tokens = 0;
            buyer_state.phase1_tokens = 0;
            buyer_state.phase2_tokens = 0;
            buyer_state.phase3_tokens = 0;
            buyer_state.last_claim_ts = 0;
        }

        require_keys_eq!(
            buyer_state.state,
            state.key(),
            PresaleError::InvalidBuyerState
        );
        require_keys_eq!(
            buyer_state.buyer,
            ctx.accounts.buyer.key(),
            PresaleError::InvalidBuyerState
        );

        // CÁLCULO CORRETO E SEGURO: Usando u128 para evitar overflow
        let tokens_per_sol = match state.current_phase {
            Phase::Whitelist => state.phase1_tokens_per_sol,
            Phase::Public => state.phase2_tokens_per_sol,
            Phase::Final => state.phase3_tokens_per_sol,
        };

        // Converter para u128 para cálculos seguros
        let lamports_128 = lamports as u128;
        let tokens_per_sol_128 = tokens_per_sol as u128;
        let token_decimals = 1_000_000_000u128;
        let sol_decimals = 1_000_000_000u128;

        // Cálculo: (lamports * tokens_per_sol * token_decimals) / sol_decimals
        let tokens_128 = lamports_128
            .checked_mul(tokens_per_sol_128)
            .and_then(|v| v.checked_mul(token_decimals))
            .and_then(|v| v.checked_div(sol_decimals))
            .ok_or(PresaleError::MathOverflow)?;

        // Converter de volta para u64 (verificando se não excede u64::MAX)
        let tokens = u64::try_from(tokens_128).map_err(|_| PresaleError::MathOverflow)?;

        // VERIFICAÇÕES COM VALORES CONSISTENTES
        match state.current_phase {
            Phase::Whitelist => {
                require!(
                    state.phase1_sold_tokens.checked_add(tokens).is_some()
                        && state.phase1_sold_tokens + tokens <= state.phase1_tokens_offered,
                    PresaleError::PhaseLimitExceeded
                );
                state.phase1_sold_tokens = state
                    .phase1_sold_tokens
                    .checked_add(tokens)
                    .ok_or(PresaleError::MathOverflow)?;
                buyer_state.phase1_tokens = buyer_state
                    .phase1_tokens
                    .checked_add(tokens)
                    .ok_or(PresaleError::MathOverflow)?;
            }
            Phase::Public => {
                require!(
                    state.phase2_sold_tokens.checked_add(tokens).is_some()
                        && state.phase2_sold_tokens + tokens <= state.phase2_tokens_offered,
                    PresaleError::PhaseLimitExceeded
                );
                state.phase2_sold_tokens = state
                    .phase2_sold_tokens
                    .checked_add(tokens)
                    .ok_or(PresaleError::MathOverflow)?;
                buyer_state.phase2_tokens = buyer_state
                    .phase2_tokens
                    .checked_add(tokens)
                    .ok_or(PresaleError::MathOverflow)?;
            }
            Phase::Final => {
                require!(
                    state.phase3_sold_tokens.checked_add(tokens).is_some()
                        && state.phase3_sold_tokens + tokens <= state.phase3_tokens_offered,
                    PresaleError::PhaseLimitExceeded
                );
                state.phase3_sold_tokens = state
                    .phase3_sold_tokens
                    .checked_add(tokens)
                    .ok_or(PresaleError::MathOverflow)?;
                buyer_state.phase3_tokens = buyer_state
                    .phase3_tokens
                    .checked_add(tokens)
                    .ok_or(PresaleError::MathOverflow)?;
            }
        }

        // Transfere SOL do comprador para a PDA
        let cpi_accounts = SystemTransfer {
            from: ctx.accounts.buyer.to_account_info(),
            to: ctx.accounts.treasury.to_account_info(),
        };

        let cpi_ctx = CpiContext::new(ctx.accounts.system_program.to_account_info(), cpi_accounts);

        system_program::transfer(cpi_ctx, lamports)?;

        // Atualiza todos os valores consistentemente
        buyer_state.contributed_lamports = buyer_state
            .contributed_lamports
            .checked_add(lamports)
            .ok_or(PresaleError::MathOverflow)?;

        buyer_state.allocated_tokens = buyer_state
            .allocated_tokens
            .checked_add(tokens)
            .ok_or(PresaleError::MathOverflow)?;

        state.total_raised_lamports = state
            .total_raised_lamports
            .checked_add(lamports)
            .ok_or(PresaleError::MathOverflow)?;

        // DEBUG: Log para verificar os valores
        msg!("=== DEBUG BUY ===");
        msg!("Lamports: {}", lamports);
        msg!("Tokens per SOL: {}", tokens_per_sol);
        msg!("Tokens calculated: {}", tokens);
        msg!("Tokens human readable: {}", tokens as f64 / 1_000_000_000.0);
        msg!("=================");

        Ok(())
    }

    /// Finaliza a venda (somente autoridade)
    pub fn finalize(ctx: Context<OnlyAuthority>) -> Result<()> {
        let clock = Clock::get()?;
        let state = &mut ctx.accounts.state;

        require!(!state.finalized, PresaleError::AlreadyFinalized);
        require!(
            clock.unix_timestamp as u64 >= state.end_ts,
            PresaleError::SaleNotEnded
        );

        state.finalized = true;
        Ok(())
    }

    /// Claim de tokens com novo sistema de vesting
    pub fn claim(ctx: Context<Claim>) -> Result<()> {
        let clock = Clock::get()?;
        let state = &ctx.accounts.state;
        let buyer_state = &mut ctx.accounts.buyer_state;

        require!(state.finalized, PresaleError::NotFinalized);
        require!(
            buyer_state.allocated_tokens > 0,
            PresaleError::NothingToClaim
        );

        let current_time = clock.unix_timestamp as u64;

        msg!("=== DEBUG CLAIM ===");
        msg!("Allocated tokens: {}", buyer_state.allocated_tokens);
        msg!("Already claimed: {}", buyer_state.claimed_tokens);
        msg!("Last claim ts: {}", buyer_state.last_claim_ts);
        msg!("TGE timestamp: {}", state.tge_ts);
        msg!("Current time: {}", current_time);

        // Calcula tokens claimáveis com novo sistema
        let claimable = compute_weekly_claimable_tokens(
            current_time,
            state.tge_ts,
            buyer_state.allocated_tokens,
            buyer_state.claimed_tokens,
            buyer_state.last_claim_ts,
        )?;

        msg!("Claimable tokens: {}", claimable);
        msg!("===================");

        require!(claimable > 0, PresaleError::NothingToClaim);

        // Transfere tokens do vault para o buyer
        let seeds = &[
            b"state".as_ref(),
            state.authority.as_ref(),
            state.mint.as_ref(),
            &[ctx.bumps.state],
        ];
        let signer = &[&seeds[..]];

        let cpi_accounts = Transfer {
            from: ctx.accounts.vault.to_account_info(),
            to: ctx.accounts.buyer_ata.to_account_info(),
            authority: ctx.accounts.state.to_account_info(),
        };
        let cpi_ctx = CpiContext::new_with_signer(
            ctx.accounts.token_program.to_account_info(),
            cpi_accounts,
            signer,
        );

        token::transfer(cpi_ctx, claimable)?;

        // Atualiza estado do buyer
        buyer_state.claimed_tokens = buyer_state
            .claimed_tokens
            .checked_add(claimable)
            .ok_or(PresaleError::MathOverflow)?;

        buyer_state.last_claim_ts = current_time;

        Ok(())
    }

    /// Transfere os fundos arrecadados (SOL) para a tesouraria
    pub fn withdraw_funds(ctx: Context<OnlyAuthority>) -> Result<()> {
        let state = &mut ctx.accounts.state;
        require!(state.finalized, PresaleError::NotFinalized);

        let amount = state.to_account_info().lamports();
        let rent_exempt = Rent::get()?.minimum_balance(std::mem::size_of::<PresaleState>());
        let transferable = amount.saturating_sub(rent_exempt);

        require!(transferable > 0, PresaleError::NothingToWithdraw);

        **state.to_account_info().try_borrow_mut_lamports()? -= transferable;
        **ctx
            .accounts
            .treasury
            .to_account_info()
            .try_borrow_mut_lamports()? += transferable;

        Ok(())
    }
}

// -----------------------------
// Contexts & Accounts
// -----------------------------

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Default)]
pub struct InitializeParams {
    pub start_ts: u64,
    pub end_ts: u64,
    pub tge_ts: u64,
    pub phase1_tokens_per_sol: u64,
    pub phase2_tokens_per_sol: u64,
    pub phase3_tokens_per_sol: u64,
    pub phase1_tokens_offered: u64,
    pub phase2_tokens_offered: u64,
    pub phase3_tokens_offered: u64,
}

#[derive(Accounts)]
#[instruction(params: InitializeParams)]
pub struct Initialize<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,
    #[account(mut)]
    pub treasury: UncheckedAccount<'info>,
    pub mint: Account<'info, Mint>,
    #[account(
        mut,
        constraint = vault.owner == state.key(),
        constraint = vault.mint == mint.key(),
    )]
    pub vault: Account<'info, TokenAccount>,
    #[account(
        init,
        payer = authority,
        space = 8 + PresaleState::SIZE,
        seeds = [b"state", authority.key().as_ref(), mint.key().as_ref()],
        bump
    )]
    pub state: Account<'info, PresaleState>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct WhitelistSet<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,
    #[account(
        mut,
        seeds = [b"state", state.authority.as_ref(), state.mint.as_ref()],
        bump
    )]
    pub state: Account<'info, PresaleState>,
    pub mint: Account<'info, Mint>,
    pub buyer: UncheckedAccount<'info>,
    #[account(
        init_if_needed,
        payer = authority,
        space = 8 + WhitelistEntry::SIZE,
        seeds = [b"whitelist", state.key().as_ref(), buyer.key().as_ref()],
        bump
    )]
    pub whitelist: Account<'info, WhitelistEntry>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct AdvancePhase<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,
    #[account(
        mut,
        seeds = [b"state", state.authority.as_ref(), state.mint.as_ref()],
        bump,
        constraint = state.authority == authority.key() @ PresaleError::Unauthorized,
    )]
    pub state: Account<'info, PresaleState>,
}

#[derive(Accounts)]
pub struct Buy<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,
    #[account(
        mut,
        seeds = [b"state", state.authority.as_ref(), state.mint.as_ref()],
        bump
    )]
    pub state: Account<'info, PresaleState>,
    #[account(
        init_if_needed,
        payer = buyer,
        space = 8 + BuyerState::SIZE,
        seeds = [b"buyer", state.key().as_ref(), buyer.key().as_ref()],
        bump
    )]
    pub buyer_state: Account<'info, BuyerState>,

    #[account(
        mut,
        constraint = treasury.key() == state.treasury @ PresaleError::InvalidInput
    )]
    pub treasury: UncheckedAccount<'info>,

    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct OnlyAuthority<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,
    #[account(
        mut,
        seeds = [b"state", state.authority.as_ref(), state.mint.as_ref()],
        bump,
        constraint = state.authority == authority.key() @ PresaleError::Unauthorized,
    )]
    pub state: Account<'info, PresaleState>,
    #[account(mut)]
    pub treasury: UncheckedAccount<'info>,
    pub token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct Claim<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,
    #[account(
        mut,
        seeds = [b"state", state.authority.as_ref(), state.mint.as_ref()],
        bump
    )]
    pub state: Account<'info, PresaleState>,
    #[account(
        mut,
        seeds = [b"buyer", state.key().as_ref(), buyer.key().as_ref()],
        bump
    )]
    pub buyer_state: Account<'info, BuyerState>,
    #[account(
        mut,
        constraint = vault.owner == state.key(),
        constraint = vault.mint == state.mint
    )]
    pub vault: Account<'info, TokenAccount>,
    #[account(
        init_if_needed,
        payer = buyer,
        associated_token::mint = mint,
        associated_token::authority = buyer
    )]
    pub buyer_ata: Account<'info, TokenAccount>,
    pub mint: Account<'info, Mint>,
    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
}

// -----------------------------
// State
// -----------------------------

#[account]
pub struct PresaleState {
    pub authority: Pubkey,
    pub mint: Pubkey,
    pub vault: Pubkey,
    pub treasury: Pubkey,
    pub start_ts: u64,
    pub end_ts: u64,
    pub tge_ts: u64,
    pub total_raised_lamports: u64,
    pub current_phase: Phase,
    pub phase1_tokens_per_sol: u64,
    pub phase2_tokens_per_sol: u64,
    pub phase3_tokens_per_sol: u64,
    pub phase1_tokens_offered: u64,
    pub phase2_tokens_offered: u64,
    pub phase3_tokens_offered: u64,
    pub phase1_sold_tokens: u64,
    pub phase2_sold_tokens: u64,
    pub phase3_sold_tokens: u64,
    pub finalized: bool,
    pub bump: u8,
}

impl PresaleState {
    pub const SIZE: usize = 32
        + 32
        + 32
        + 32
        + 8
        + 8
        + 8
        + 2
        + 8
        + 8
        + 8
        + 8
        + 8
        + 1
        + 8
        + 8
        + 8
        + 8
        + 8
        + 8
        + 8
        + 8
        + 8
        + 1
        + 1;
}

#[account]
pub struct BuyerState {
    pub state: Pubkey,
    pub buyer: Pubkey,
    pub contributed_lamports: u64,
    pub allocated_tokens: u64,
    pub claimed_tokens: u64,
    pub phase1_tokens: u64,
    pub phase2_tokens: u64,
    pub phase3_tokens: u64,
    pub last_claim_ts: u64,
}

impl BuyerState {
    pub const SIZE: usize = 32 + 32 + 8 + 8 + 8 + 8 + 8 + 8 + 8;
}

#[account]
pub struct WhitelistEntry {
    pub state: Pubkey,
    pub buyer: Pubkey,
}

impl WhitelistEntry {
    pub const SIZE: usize = 32 + 32;
}

// -----------------------------
// Helpers
// -----------------------------

/// Calcula tokens claimáveis com novo sistema: 40% no TGE + 7.5% por semana
fn compute_weekly_claimable_tokens(
    current_time: u64,
    tge_ts: u64,
    allocated_tokens: u64,
    already_claimed: u64,
    last_claim_ts: u64,
) -> Result<u64> {
    if current_time < tge_ts {
        return Ok(0);
    }

    // 40% no TGE
    let tge_tokens = (allocated_tokens * 4000) / (BPS_MAX as u64);

    // Primeiro claim: recebe TGE
    if last_claim_ts == 0 {
        return Ok(tge_tokens);
    }

    // Se ainda não claimou todo TGE
    if already_claimed < tge_tokens {
        return Ok(tge_tokens - already_claimed);
    }

    // Calcula semanas desde TGE
    let weeks_since_tge = (current_time - tge_ts) / WEEK_SECONDS;

    if weeks_since_tge == 0 {
        return Ok(0);
    }

    // Tokens restantes (60%)
    let remaining_tokens = allocated_tokens - tge_tokens;

    // 7.5% por semana dos tokens restantes
    let weekly_release = (remaining_tokens * (RELEASE_PERCENTAGE as u64)) / (BPS_MAX as u64);

    // Total que deveria estar liberado
    let total_released = tge_tokens + (weekly_release * weeks_since_tge as u64);
    let total_released = total_released.min(allocated_tokens);

    // Claimable = total liberado - já claimado
    Ok(total_released.saturating_sub(already_claimed))
}

// -----------------------------
// Errors
// -----------------------------
#[error_code]
pub enum PresaleError {
    #[msg("Unauthorized")]
    Unauthorized,
    #[msg("Invalid BPS")]
    InvalidBps,
    #[msg("Invalid time configuration")]
    InvalidTime,
    #[msg("Invalid caps")]
    InvalidCap,
    #[msg("Sale not started")]
    SaleNotStarted,
    #[msg("Sale already ended")]
    SaleEnded,
    #[msg("Sale not ended")]
    SaleNotEnded,
    #[msg("Sale already finalized")]
    AlreadyFinalized,
    #[msg("Hard cap exceeded")]
    HardCapExceeded,
    #[msg("Per-wallet limit exceeded")]
    PerWalletLimitExceeded,
    #[msg("Math overflow")]
    MathOverflow,
    #[msg("Invalid vault mint")]
    InvalidVaultMint,
    #[msg("Invalid vault owner")]
    InvalidVaultOwner,
    #[msg("Invalid whitelist account")]
    InvalidWhitelist,
    #[msg("Invalid buyer state")]
    InvalidBuyerState,
    #[msg("Nothing to claim")]
    NothingToClaim,
    #[msg("Nothing to withdraw")]
    NothingToWithdraw,
    #[msg("Not finalized")]
    NotFinalized,
    #[msg("Phase limit exceeded")]
    PhaseLimitExceeded,
    #[msg("Already in final phase")]
    AlreadyFinalPhase,
    #[msg("Invalid input")]
    InvalidInput,
    #[msg("Batch too large")]
    BatchTooLarge,
}
