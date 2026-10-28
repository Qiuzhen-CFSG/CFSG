module
public import Theory.GroupTheory.HeisenbergNormalizedSubgroups
public import Theory.GroupTheory.CentralSectionNormalComplement
public import Theory.GroupTheory.Fitting.PGroup
public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Centralizers of normal Heisenberg three-groups

A normal Heisenberg group of order 27 in a group of three-rank at most two
has cyclic three-centralizer when the ambient three-prime core is trivial.
Every elementary abelian subgroup of the centralizer lies in the marked
central cubic. Burnside transfer supplies a normal three-complement, which
vanishes in the ambient three-prime core.

Source application: Aschbacher–Smith 14.7.15(3), printed p.1047,
refs/quasithin.pdf. No equality with the ambient two-residual is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Subgroup

/-- The centralizer of a normal Heisenberg27 is a cyclic three-group under
the ambient three-rank and three-prime-core bounds. -/
theorem heisenberg_centralizer_isCyclic_threeGroup
    {D : Type*} [Group D] [Finite D]
    (R : Subgroup D) [R.Normal] (e : R ≃* HeisenbergPrime 3)
    (hr : primeRank 3 D ≤ 2) (hcore : pPrimeCore 3 D = ⊥) :
    IsPGroup 3 (centralizer (R : Set D)) ∧ IsCyclic (centralizer (R : Set D)) := by
  let C := centralizer (R : Set D)
  let Z := (center R).map R.subtype
  have hZC : Z ≤ C := by
    dsimp only [Z,C]
    rw [map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  have hZcard : Nat.card Z = 3 := by
    rw [card_map_of_injective R.subtype_injective,
      Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center]
  have elementary_bound (E : Subgroup C) (hE : IsElementaryAbelian 3 E) :
      Nat.card E ≤ 3 := by
    let := hE
    have hEZ : E.map C.subtype ≤ Z := by
      rintro _ ⟨x,hx,rfl⟩
      apply cubic_mem_center_of_centralizes_heisenberg R e hr
      · exact congrArg (fun a : E => ((a : C) : D))
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 3 E) ⟨x,hx⟩)
      · exact x.property
    have hh := card_le_of_le hEZ
    rwa [card_map_of_injective C.subtype_injective,hZcard] at hh
  let S : Sylow 3 C := default
  let : IsCyclic S := S.isCyclic_of_odd_of_elementary_card_le (by decide) elementary_bound
  let A := Z.subgroupOf C
  have hAc : Nat.card A = 3 := (Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv).trans hZcard
  have hAZ : A ≤ center C := by
    intro a ha
    apply mem_center_iff.mpr
    intro b
    obtain ⟨z,hz,heq⟩ := ha
    apply Subtype.ext
    change (b : D) * (a : D) = (a : D) * (b : D)
    change (z : D) = (a : D) at heq
    rw [←heq]
    exact (b.property z z.property).symm
  let : A.Normal := ⟨fun a ha b => by
    rw [mem_center_iff.mp (hAZ ha) b,mul_assoc,mul_inv_cancel,mul_one]
    exact ha⟩
  have hcomm : ⁅A,(⊤ : Subgroup C)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hAZ.trans (center_le_centralizer _))
  have hcomp : HasNormalPComplement 3 C :=
    S.hasNormalPComplement_of_cyclic_of_central_section A ⊥
      (by rw [hAc]) (by simp) hcomm.le
  have hCcore : pPrimeCore 3 C = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    exact bot_unique ((pPrimeCore_map_subtype_le_pPrimeCore_of_normal 3 C).trans_eq hcore)
  have hp := isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 3 C hcomp
  have hCp : IsPGroup 3 C := hp.of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hCcore).trans QuotientGroup.quotientBot)
  exact ⟨hCp,hCp.isCyclic_of_odd_of_elementary_card_le (by decide) elementary_bound⟩

end Subgroup
