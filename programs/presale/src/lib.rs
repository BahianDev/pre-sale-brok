use anchor_lang::prelude::*;
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token::{self, Mint, Token, TokenAccount, Transfer};

declare_id!("H8f7TyKannRfECDjYqEpiMXjqDxAxjfRLRBaL2op2Kcx");

// -----------------------------
// Constantes
// -----------------------------
const BPS_MAX: u16 = 10_000;

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

        require!(params.tge_bps <= BPS_MAX, PresaleError::InvalidBps);
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
        state.tge_bps = params.tge_bps;
        state.cliff_seconds = params.cliff_seconds;
        state.vesting_seconds = params.vesting_seconds;

        state.soft_cap_lamports = params.soft_cap_lamports;
        state.hard_cap_lamports = params.hard_cap_lamports;
        state.total_raised_lamports = 0;

        // Configuração das fases
        state.current_phase = Phase::Whitelist;
        state.phase1_tokens_per_sol = params.phase1_tokens_per_sol; // 1000 tokens por SOL (0.001 SOL cada)
        state.phase2_tokens_per_sol = params.phase2_tokens_per_sol; // 100 tokens por SOL (0.01 SOL cada)
        state.phase3_tokens_per_sol = params.phase3_tokens_per_sol; // 66.666 tokens por SOL (0.015 SOL cada)

        state.phase1_tokens_offered = params.phase1_tokens_offered;
        state.phase2_tokens_offered = params.phase2_tokens_offered;
        state.phase3_tokens_offered = params.phase3_tokens_offered;

        state.phase1_sold_tokens = 0;
        state.phase2_sold_tokens = 0;
        state.phase3_sold_tokens = 0;

        state.finalized = false;
        state.canceled = false;

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

    /// Define ou atualiza a alocação máxima (em lamports) para um comprador whitelistado.
    pub fn whitelist_set(ctx: Context<WhitelistSet>, max_contribution_lamports: u64) -> Result<()> {
        let state = &ctx.accounts.state;
        require!(
            state.authority == ctx.accounts.authority.key(),
            PresaleError::Unauthorized
        );
        require!(!state.finalized, PresaleError::AlreadyFinalized);

        let w = &mut ctx.accounts.whitelist;
        w.state = state.key();
        w.buyer = ctx.accounts.buyer.key();
        w.max_contribution_lamports = max_contribution_lamports;
        Ok(())
    }

    /// Avança para a próxima fase (somente autoridade)
    pub fn advance_phase(ctx: Context<AdvancePhase>) -> Result<()> {
        let state = &mut ctx.accounts.state;

        require!(!state.finalized, PresaleError::AlreadyFinalized);
        require!(!state.canceled, PresaleError::SaleCanceled);

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

        require!(!state.canceled, PresaleError::SaleCanceled);
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
                // Na fase whitelist, verifica se o comprador está na whitelist
                let wl = &ctx.accounts.whitelist;

                require_keys_eq!(wl.state, state.key(), PresaleError::InvalidWhitelist);
                require_keys_eq!(
                    wl.buyer,
                    ctx.accounts.buyer.key(),
                    PresaleError::InvalidWhitelist
                );
                require!(
                    lamports <= wl.max_contribution_lamports,
                    PresaleError::PerWalletLimitExceeded
                );
            }
            Phase::Public | Phase::Final => {
                // Fases públicas - qualquer um pode comprar
                // Não precisa fazer verificações de whitelist
            }
        }

        // Checa caps globais
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

        // Verifica se há tokens disponíveis na fase
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

        // Transfere SOL (lamports) do comprador para a PDA (conta `state`)
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

        // Atualiza totals
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

    /// Finaliza a venda (somente autoridade), se soft cap atingido e período encerrado.
    pub fn finalize(ctx: Context<OnlyAuthority>) -> Result<()> {
        let clock = Clock::get()?;
        let state = &mut ctx.accounts.state;

        require!(!state.finalized, PresaleError::AlreadyFinalized);
        require!(!state.canceled, PresaleError::SaleCanceled);
        require!(
            clock.unix_timestamp as u64 >= state.end_ts,
            PresaleError::SaleNotEnded
        );
        require!(
            state.total_raised_lamports >= state.soft_cap_lamports,
            PresaleError::SoftCapNotMet
        );

        state.finalized = true;
        Ok(())
    }

    /// Cancela a venda (permite refund).
    pub fn cancel(ctx: Context<OnlyAuthority>) -> Result<()> {
        let state = &mut ctx.accounts.state;
        require!(!state.finalized, PresaleError::AlreadyFinalized);
        state.canceled = true;
        Ok(())
    }

    /// Refund para o comprador se a venda terminou sem atingir soft cap ou foi cancelada.
    pub fn refund(ctx: Context<Refund>) -> Result<()> {
        let clock = Clock::get()?;
        let state = &mut ctx.accounts.state;
        let buyer_state = &mut ctx.accounts.buyer_state;

        let ended = clock.unix_timestamp as u64 > state.end_ts;
        require!(
            state.canceled || (ended && state.total_raised_lamports < state.soft_cap_lamports),
            PresaleError::RefundNotAvailable
        );
        require!(
            buyer_state.contributed_lamports > 0,
            PresaleError::NothingToRefund
        );

        let amount = buyer_state.contributed_lamports;
        buyer_state.contributed_lamports = 0;
        buyer_state.allocated_tokens = 0;
        buyer_state.phase1_tokens = 0;
        buyer_state.phase2_tokens = 0;
        buyer_state.phase3_tokens = 0;

        // Transfere lamports da PDA `state` para o comprador
        **state.to_account_info().try_borrow_mut_lamports()? -= amount;
        **ctx
            .accounts
            .buyer
            .to_account_info()
            .try_borrow_mut_lamports()? += amount;

        Ok(())
    }

    /// Claim de tokens de acordo com o cronograma de vesting.
    /// IMPORTANTE: Apenas 40% dos tokens comprados estão disponíveis para claim
    /// 60% estão locked permanentemente
    pub fn claim(ctx: Context<Claim>) -> Result<()> {
        let clock = Clock::get()?;
        let state = &ctx.accounts.state;
        let buyer_state = &mut ctx.accounts.buyer_state;

        require!(state.finalized, PresaleError::NotFinalized);
        require!(
            buyer_state.allocated_tokens > 0,
            PresaleError::NothingToClaim
        );

        // Calcula o total de tokens disponíveis para claim (40% do total alocado)
        let total_claimable_tokens = mul_div_u128(
            buyer_state.allocated_tokens as u128,
            4000, // 40% em BPS
            BPS_MAX as u128,
        ).map_err(|_| PresaleError::MathOverflow)? as u64;

        let vested_bps = compute_vested_bps(
            clock.unix_timestamp as u64,
            state.tge_ts,
            state.tge_bps,
            state.cliff_seconds,
            state.vesting_seconds,
        );

        let vested_tokens = mul_div_u128(
            total_claimable_tokens as u128,
            vested_bps as u128,
            BPS_MAX as u128,
        ).map_err(|_| PresaleError::MathOverflow)? as u64;

        let claimable = vested_tokens
            .checked_sub(buyer_state.claimed_tokens)
            .ok_or(PresaleError::MathOverflow)?;

        require!(claimable > 0, PresaleError::NothingToClaim);

        // Transfere do vault (ATA da PDA) para o ATA do comprador
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

        buyer_state.claimed_tokens = buyer_state
            .claimed_tokens
            .checked_add(claimable)
            .ok_or(PresaleError::MathOverflow)?;
        Ok(())
    }

    /// Transfere os fundos arrecadados (SOL) para a tesouraria, somente após finalização.
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
    pub tge_bps: u16,
    pub cliff_seconds: u64,
    pub vesting_seconds: u64,
    pub soft_cap_lamports: u64,
    pub hard_cap_lamports: u64,

    // Configuração das fases
    pub phase1_tokens_per_sol: u64, // 1000 tokens por SOL (preço 0.001 SOL)
    pub phase2_tokens_per_sol: u64, // 100 tokens por SOL (preço 0.01 SOL)
    pub phase3_tokens_per_sol: u64, // 66.666 tokens por SOL (preço 0.015 SOL)

    pub phase1_tokens_offered: u64, // 17,422,222 tokens
    pub phase2_tokens_offered: u64, // 16,447,368 tokens
    pub phase3_tokens_offered: u64, // 15,555,556 tokens
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

    /// Whitelist account - só é obrigatória na Phase::Whitelist
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
pub struct Refund<'info> {
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
    pub tge_bps: u16,
    pub cliff_seconds: u64,
    pub vesting_seconds: u64,

    pub soft_cap_lamports: u64,
    pub hard_cap_lamports: u64,
    pub total_raised_lamports: u64,

    // Configuração das fases
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
    pub canceled: bool,

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
}
impl BuyerState {
    pub const SIZE: usize = 32 + 32 + 8 + 8 + 8 + 8 + 8 + 8;
}

#[account]
pub struct WhitelistEntry {
    pub state: Pubkey,
    pub buyer: Pubkey,
    pub max_contribution_lamports: u64,
}
impl WhitelistEntry {
    pub const SIZE: usize = 32 + 32 + 8;
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

fn compute_vested_bps(
    now_ts: u64,
    tge_ts: u64,
    tge_bps: u16,
    cliff_seconds: u64,
    vesting_seconds: u64,
) -> u16 {
    if now_ts < tge_ts {
        return 0;
    }
    let mut total_bps = tge_bps as u64;

    let cliff_end = tge_ts.saturating_add(cliff_seconds);
    if vesting_seconds == 0 {
        return total_bps.min(BPS_MAX as u64) as u16;
    }
    if now_ts <= cliff_end {
        return total_bps.min(BPS_MAX as u64) as u16;
    }

    let elapsed = now_ts.saturating_sub(cliff_end);
    let linear_bps_max = (BPS_MAX as u64).saturating_sub(total_bps);
    let linear_bps = if elapsed >= vesting_seconds {
        linear_bps_max
    } else {
        (elapsed as u128)
            .saturating_mul(linear_bps_max as u128)
            .checked_div(vesting_seconds as u128)
            .unwrap_or(0) as u64
    };

    total_bps = total_bps.saturating_add(linear_bps);
    total_bps.min(BPS_MAX as u64) as u16
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
    #[msg("Soft cap not met")]
    SoftCapNotMet,
    #[msg("Sale already finalized")]
    AlreadyFinalized,
    #[msg("Sale canceled")]
    SaleCanceled,
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
    #[msg("Nothing to refund")]
    NothingToRefund,
    #[msg("Nothing to claim")]
    NothingToClaim,
    #[msg("Nothing to withdraw")]
    NothingToWithdraw,
    #[msg("Refund not available")]
    RefundNotAvailable,
    #[msg("Not finalized")]
    NotFinalized,
    #[msg("Phase limit exceeded")]
    PhaseLimitExceeded,
    #[msg("Already in final phase")]
    AlreadyFinalPhase,
}
