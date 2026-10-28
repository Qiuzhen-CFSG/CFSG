module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceResiduals
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Inputs

/-!
# Applying the terminal residual comparison to the actual marked flag

The order-two flag line and its outside marked vector generate the
order-four flag plane. This identifies the earlier T-invariant V₂ with
⟨z,v⟩. The source-correct residual Thompson argument can therefore use
FlagSource and FlagMarking directly, without an extra plane identification
or residual-normalization premise. The residual identity and orthogonal
Thompson equality still belong to the rank-four model argument.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the flag on
printed p.926 and the concluding paragraph on printed p.933.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
variable {G : Type*} [Group G] [Finite G]

/-- The marked vector outside the flag line generates the entire plane with z. -/
theorem plane_eq_of_flagMarking {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : A5Module.FlagSource T L V V₁ V₂) (f : A5Module.FlagMarking T L V V₁ V₂) :
    V₂ = zpowers (A5Module.markedZ f.module) ⊔ zpowers (A5Module.markedV f.module) := by
  let J := zpowers (A5Module.markedZ f.module) ⊔ zpowers (A5Module.markedV f.module)
  have h₁ : V₁ ≤ J := by rw [← f.line_eq]; exact le_sup_left
  have h₂ : J ≤ V₂ := sup_le (by rw [f.line_eq]; exact d.one_le_two) (zpowers_le.mpr f.vector_mem)
  have hv : A5Module.markedV f.module ∈ J := (show zpowers (A5Module.markedV f.module) ≤ J from le_sup_right) (mem_zpowers _)
  have hgt : 2 < Nat.card J := by
    by_contra! hle
    have he : V₁ = J := eq_of_le_of_card_ge h₁ (by rwa [d.one_card])
    exact f.vector_not_mem (he.ge hv)
  have hdiv : 2 ∣ Nat.card J := d.one_card ▸ card_dvd_of_le h₁
  have hge : 4 ≤ Nat.card J := by
    obtain ⟨n, hn⟩ := hdiv
    omega
  exact (eq_of_le_of_card_ge h₂ (by rwa [d.two_card])).symm

/-- The final residual argument with its geometric inputs discharged by
the existing source flag. -/
theorem false_of_flag_residual_thompson_comparison
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : A5Module.FlagSource T L V V₁ V₂) (f : A5Module.FlagMarking T L V V₁ V₂)
    (K : Subgroup G)
    (hK : K = (primeToResidual 3 (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype)
    (hidx : (Tv (T : Subgroup G) (A5Module.markedV f.module)).relIndex (T : Subgroup G) = 2)
    (hJ : elementaryAbelianMaxJ ((orthogonalResidual K (A5Module.markedZ f.module) ⊔
      Tv (T : Subgroup G) (A5Module.markedV f.module)).pCoreIn 2) =
      elementaryAbelianMaxJ ((K ⊔ Tv (T : Subgroup G) (A5Module.markedV f.module)).pCoreIn 2))
    (h16 : (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥) : False := by
  apply false_of_residual_thompson_comparison T K V₂
    (A5Module.markedZ f.module) (A5Module.markedV f.module) hK
    (plane_eq_of_flagMarking d f) d.two_invariant
    (d.V_le_T (d.two_le_V f.vector_mem)) _ hidx hJ h16
  intro hv
  exact f.vector_not_mem (by rw [hv]; exact V₁.one_mem)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
