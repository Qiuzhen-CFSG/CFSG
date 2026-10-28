module
public import Theory.GroupTheory.CComponent.DoubleWreath
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.PSL2.BinaryOuter
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder

/-!
# The actual components of Aut(PSL₂(16)) wr C₂

The binary outer quotient is solvable and the inner group is perfect,
so the solvable residual of Aut(PSL₂(16)) is its inner subgroup. The
double-wreath component theorem identifies each component with PSL₂(16).
Passing through the literal ambient two-core quotient then identifies
each original C-component modulo its own two-core.

Only the five-divisibility needed for exact-order-five generation is
recorded; the source argument uses these concrete quotient equivalences.
Source: Aschbacher--Smith14.6.14(4) and14.6.15, printed pp.1033--1034;
GLS3, Theorem2.5.12, for binary automorphisms.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2.SixteenWreathComponents
abbrev L := PSL(2,GaloisField 2 4)
abbrev W := RegularWreathProduct (MulAut L) (Multiplicative (ZMod 2))

theorem simple : IsSimpleGroup L :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [GaloisField.card 2 4 (by decide)]; decide)

theorem perfect : Group.IsPerfect L := by
  obtain ⟨x,hx,hx1⟩ := BenderSuzuki.Converse.exists_ne_zero_ne_one 4 (by decide)
  exact ⟨SL2Simple.PSL_commutator_eq_top ⟨x,hx,fun hs => by
    rcases sq_eq_one_iff.mp hs with hs | hs
    · exact hx1 hs
    · exact hx1 (by simpa only [CharTwo.neg_eq] using hs)⟩⟩

private theorem center_eq_bot : center L = ⊥ := by
  let := simple
  let := perfect
  exact (inferInstance : (center L).Normal).eq_bot_or_eq_top.resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp he))

/-- The original automorphism group's residual is its actual inner subgroup. -/
theorem aut_residual_eq_inner : solvableResidual (MulAut L) = MulAut.innerSubgroup L := by
  let := perfect
  let : Group.IsPerfect (MulAut.innerSubgroup L) := Group.IsPerfect.range MulAut.conj
  let : Group.IsSolvable (MulAut.Outer L) :=
    binary_outer_isSolvable_of_mulEquiv (GaloisField 2 4) (MulEquiv.refl L)
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)

noncomputable def autResidualEquiv : solvableResidual (MulAut L) ≃* L :=
  (MulEquiv.subgroupCongr aut_residual_eq_inner).trans
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).symm

private theorem residual_quasisimple : IsQuasisimple (solvableResidual (MulAut L)) := by
  let := simple
  let := perfect
  let e := autResidualEquiv
  let : IsSimpleGroup (solvableResidual (MulAut L)) := e.isSimpleGroup
  let : Group.IsPerfect (solvableResidual (MulAut L)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center (solvableResidual (MulAut L)) = ⊥ :=
    (inferInstance : (center (solvableResidual (MulAut L))).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩

/-- Every C-component of the literal wreath model is PSL₂(16). -/
theorem component_equiv {K : Subgroup W} (hK : K.IsCComponent) :
    Nonempty (K ≃* L) := by
  obtain ⟨e⟩ := CComponentDoubleWreath.component_equiv (MulAut L) residual_quasisimple hK
  exact ⟨e.trans autResidualEquiv⟩

/-- Transport through the original ambient two-core quotient. -/
theorem coreQuotient_component_equiv {D : Type*} [_root_.Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* W) {K : Subgroup D} (hK : K.IsCComponent) :
    Nonempty ((K ⧸ pCore 2 K) ≃* L) := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
  obtain ⟨a⟩ := component_equiv ((hK.map_quotient (pCore 2 D)).map_equiv e)
  exact ⟨(cComponentTwoCoreQuotientEquiv hK).trans ((e.subgroupMap (K.map q)).trans a)⟩

/-- Five divides the model quotient, as required by the source operation θ. -/
theorem five_dvd_card : 5 ∣ Nat.card L := by
  rw [←Nat.card_congr (Atlas.RankOneFieldAutomorphisms.slEquivPSL
    (F := GaloisField 2 4)).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,
    GaloisField.card 2 4 (by decide)]
  decide

private theorem aut_pow_five_mem_residual (x : MulAut L) (hx : x ^ 5 = 1) :
    x ∈ solvableResidual (MulAut L) := by
  rw [aut_residual_eq_inner]
  let q := QuotientGroup.mk' (MulAut.innerSubgroup L)
  have hc : Nat.card (MulAut.Outer L) = 4 :=
    Theory.PSL2.outer_card_eq_field_degree (GaloisField 2 4)
      (GaloisField.card 2 4 (by decide))
  have h5 : orderOf (q x) ∣ 5 := orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hx,map_one])
  have h4 : orderOf (q x) ∣ 4 := by
    have hh := _root_.orderOf_dvd_natCard (q x)
    change orderOf (q x) ∣ Nat.card (MulAut.Outer L) at hh
    rwa [hc] at hh
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 4) h5 h4))

/-- Every quintic element lies in the two actual distinct components. -/
theorem quintic_mem_component_pair {A B : Subgroup W}
    (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B)
    {x : W} (hx : x ^ 5 = 1) : x ∈ A ⊔ B :=
  CComponentDoubleWreath.mem_component_pair_of_pow_five (MulAut L)
    residual_quasisimple aut_pow_five_mem_residual hA hB hne hx
end Theory.PSL2.SixteenWreathComponents
