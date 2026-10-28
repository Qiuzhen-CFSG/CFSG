module

public import Theory.Representation.SymplecticFour.BinaryDegree
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.GroupAction.NormalPChiefSeries.Linear
/-!
# Chief degrees above a nonbinary symplectic two-core quotient

Every nontrivial representation of Sp₄(2ᵐ), m≥2, is faithful, by simplicity
of the literal centerless matrix group. The binary primitive-prime bound
therefore forces degree at least 4m. Descending only an irreducible chief
action through its normal two-core gives the bound on every actual noncentral
chief factor. No descent of a possibly reducible whole module is assumed.

Source: Aschbacher–Smith E.2.13(4) and E.2.15, printed pp.225,228.
-/

public section
open Subgroup Representation Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups IsMulCommutative
namespace Representation.SymplecticFour
variable {H K W : Type*} [Group H] [Finite H] [Field K] [Finite K] [CharP K 2]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem core_quotient_irreducible_finrank_bound
    (e : (H ⧸ pCore 2 H) ≃* Sp K)
    (ρ : Representation (ZMod 2) H W) [ρ.IsIrreducible]
    (hn : ∃ h, ρ h ≠ 1) (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card K = 2 ^ m) :
    4 * m ≤ Module.finrank (ZMod 2) W := by
  have hk : pCore 2 H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let τ := quotientOfLEKer ρ (pCore 2 H) hk
  let σ := τ.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  have hnσ : ∃ g, σ g ≠ 1 := by
    obtain ⟨h, hh⟩ := hn
    refine ⟨e (QuotientGroup.mk' (pCore 2 H) h), ?_⟩
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, τ, quotientOfLEKer_apply] using hh
  have hF : 3 < Nat.card K := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hm
    rw [hcard]
    omega
  let : IsSimpleGroup (Sp K ⧸ center (Sp K)) := SimpleQuotients.isSimpleGroup hF
  let : IsSimpleGroup (Sp K) := (EvenProjective.equiv (F := K)).isSimpleGroup
  have hσ : Function.Injective σ := by
    apply σ.ker_eq_bot_iff.mp
    rcases σ.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact hk
    obtain ⟨g,hg⟩ := hnσ
    exact (hg (show g ∈ σ.ker from hk ▸ mem_top g)).elim
  exact finrank_ge (by omega) hcard σ hσ

end Representation.SymplecticFour

namespace NoncentralChiefRefinement.SeriesOn
variable {H K : Type*} [Group H] [Finite H] [Field K] [Finite K] [CharP K 2]
  {U : Subgroup H} [U.Normal] [IsElementaryAbelian 2 U]
theorem noncentral_factor_finrank_ge_symplectic_four
    (e : (H ⧸ pCore 2 H) ≃* Sp K)
    (s : SeriesOn U) (i : Fin s.series.length) (hi : ¬ s.Central i)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card K = 2 ^ m) :
    4 * m ≤ Module.finrank (ZMod 2) (Additive (s.Factor i)) := by
  let := s.factorRepresentation_irreducible i
  apply Representation.SymplecticFour.core_quotient_irreducible_finrank_bound e
    (s.factorRepresentation i) ?_ m hm hcard
  by_contra! hn
  apply hi
  rw [s.central_iff_action]
  intro h x
  exact congrArg Additive.toMul (congrArg (fun f => f (Additive.ofMul x)) (hn h))
end NoncentralChiefRefinement.SeriesOn
