use anchor_lang::prelude::*;
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token::{self, Mint, Token, TokenAccount, Transfer};

declare_id!("H8f7TyKannRfECDjYqEpiMXjqDxAxjfRLRBaL2op2Kcx");

// -----------------------------
// Constantes
// -----------------------------
const BPS_MAX: u16 = 10_000;
const WEEK_SECONDS: u64 = 7 * 24 * 60 * 60; // 7 dias em segundos
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

        require!(params.start_ts < params.end_ts, PresaleError::InvalidTime);
        require!(params.hard_cap_lamports > 0, PresaleError::InvalidCap);
        require!(
            params.soft_cap_lamports <= params.hard_cap_lamports,
            PresaleError::InvalidCap
        );

        state.authority = ctx.accounts.authority.key();
        state.mint = ctx.accounts.mint.key();
        state.vault = ctx.accounts.vault.key();
        state.treasury = ctx.accounts.treasury.key();

        state.start_ts = params.start_ts;
        state.end_ts = params.end_ts;

        state.tge_ts = params.tge_ts;

        state.soft_cap_lamports = params.soft_cap_lamports;
        state.hard_cap_lamports = params.hard_cap_lamports;
        state.total_raised_lamports = 0;

        // Configuração das fases
        state.current_phase = Phase::Whitelist;
        state.phase1_tokens_per_sol = params.phase1_tokens_per_sol;
        state.phase2_tokens_per_sol = params.phase2_tokens_per_sol;
        state.phase3_tokens_per_sol = params.phase3_tokens_per_sol;

        state.phase1_tokens_offered = params.phase1_tokens_offered;
        state.phase2_tokens_offered = params.phase2_tokens_offered;
        state.phase3_tokens_offered = params.phase3_tokens_offered;

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

    /// Compra (envia SOL). Registra contribuição e aloca tokens pelo preço da fase atual.
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

        // Verifica se a fase atual permite a compra
        match state.current_phase {
            Phase::Whitelist => {
                let wl = &ctx.accounts.whitelist;
                require_keys_eq!(wl.state, state.key(), PresaleError::InvalidWhitelist);
                require_keys_eq!(
                    wl.buyer,
                    ctx.accounts.buyer.key(),
                    PresaleError::InvalidWhitelist
                );
                // Sem limite de contribuição para whitelist - apenas verifica se está na lista
            }
            Phase::Public | Phase::Final => {}
        }

        require!(
            state.total_raised_lamports + lamports <= state.hard_cap_lamports,
            PresaleError::HardCapExceeded
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

        // Calcula tokens baseado na fase atual
        let tokens_per_sol = match state.current_phase {
            Phase::Whitelist => state.phase1_tokens_per_sol,
            Phase::Public => state.phase2_tokens_per_sol,
            Phase::Final => state.phase3_tokens_per_sol,
        };

        let tokens = mul_div_u128(lamports as u128, tokens_per_sol as u128, 1_000_000_000u128)
            .map_err(|_| PresaleError::MathOverflow)? as u64;

        match state.current_phase {
            Phase::Whitelist => {
                require!(
                    state.phase1_sold_tokens + tokens <= state.phase1_tokens_offered,
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
                    state.phase2_sold_tokens + tokens <= state.phase2_tokens_offered,
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
                    state.phase3_sold_tokens + tokens <= state.phase3_tokens_offered,
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
        let ix = anchor_lang::solana_program::system_instruction::transfer(
            &ctx.accounts.buyer.key(),
            &state.key(),
            lamports,
        );
        anchor_lang::solana_program::program::invoke(
            &ix,
            &[
                ctx.accounts.buyer.to_account_info(),
                state.to_account_info(),
                ctx.accounts.system_program.to_account_info(),
            ],
        )?;

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
        
        // Calcula tokens claimáveis com novo sistema
        let claimable = compute_weekly_claimable_tokens(
            current_time,
            state.tge_ts,
            buyer_state.allocated_tokens,
            buyer_state.claimed_tokens,
            buyer_state.last_claim_ts,
        )?;

        require!(claimable > 0, PresaleError::NothingToClaim);

        // Transfere tokens do vault para o buyer
        let seeds = &[
            b"state".as_ref(),
            state.authority.as_ref(),
            state.mint.as_ref(),
            &[state.bump],
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
    pub soft_cap_lamports: u64,
    pub hard_cap_lamports: u64,
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
        bump = state.bump
    )]
    pub state: Account<'info, PresaleState>,
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
        bump = state.bump,
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
        bump = state.bump
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
        seeds = [b"whitelist", state.key().as_ref(), buyer.key().as_ref()],
        bump
    )]
    pub whitelist: Account<'info, WhitelistEntry>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct OnlyAuthority<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,
    #[account(
        mut,
        seeds = [b"state", state.authority.as_ref(), state.mint.as_ref()],
        bump = state.bump,
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
        bump = state.bump
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
    pub soft_cap_lamports: u64,
    pub hard_cap_lamports: u64,
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
    pub const SIZE: usize = 32 + 32 + 32 + 32 + 8 + 8 + 8 + 2 + 8 + 8 + 8 + 8 + 8 + 1 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 1 + 1;
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

fn mul_div_u128(a: u128, b: u128, denom: u128) -> std::result::Result<u128, PresaleError> {
    if let Some(product) = a.checked_mul(b) {
        if let Some(result) = product.checked_div(denom) {
            Ok(result)
        } else {
            Err(PresaleError::MathOverflow)
        }
    } else {
        Err(PresaleError::MathOverflow)
    }
}

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

    // 40% disponível imediatamente no TGE
    let tge_tokens = mul_div_u128(allocated_tokens as u128, 4000, BPS_MAX as u128)
        .map_err(|_| PresaleError::MathOverflow)? as u64;

    // Se nunca claimou antes, claima os 40% do TGE
    if last_claim_ts == 0 {
        return Ok(tge_tokens);
    }

    // Calcula semanas passadas desde o último claim
    let time_since_last_claim = current_time.saturating_sub(last_claim_ts);
    let weeks_passed = time_since_last_claim / WEEK_SECONDS;

    if weeks_passed == 0 {
        return Ok(0);
    }

    // Tokens restantes após TGE (60%)
    let remaining_tokens = allocated_tokens.saturating_sub(tge_tokens);
    
    // 7.5% dos tokens restantes por semana
    let tokens_per_week = mul_div_u128(remaining_tokens as u128, RELEASE_PERCENTAGE as u128, BPS_MAX as u128)
        .map_err(|_| PresaleError::MathOverflow)? as u64;

    // Total claimável desde o último claim
    let newly_claimable = tokens_per_week * weeks_passed as u64;

    // Garante que não claima mais do que o total disponível
    let total_claimable = tge_tokens + remaining_tokens;
    let max_claimable_now = total_claimable.saturating_sub(already_claimed);

    Ok(newly_claimable.min(max_claimable_now))
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