module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryLinear
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryLinear

/-!
# Direct BinaryLinear ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.BinaryLinear. The original residual input and literal
marked Sylow supply its geometric hypotheses without a partner residual identity.
The deliberate private import keeps those existing model lemmas internal.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
open Section01 Section03 Candidates.ComponentStructure ClassificationModels OrdinaryComponents
open BinaryLinear BinaryLinear.OuterCyclic BinaryNaturalDual.VectorStabilizers
open ChapterB.QuasisimpleSource.NaturalDualCentralizer DoubleCoverCentralizer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
variable (hcard : Nat.card (centralInvolutions T) = 2)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include r hcard

/-- Both binary linear rows of15.2.24 are impossible on the original component. -/
theorem not_binary_linear_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL c.component n 2)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let eq := (e.trans (Atlas.fieldEquivPSL n ef)).trans (projectiveEquivLinear (by omega))
  let : Finite (LinearGroup n) := Finite.of_equiv c.component eq.toEquiv
  have hc : center c.component = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr (eq.trans (slEquivLinear n).symm) ⟨x,hx⟩).property
    change (slEquivLinear n).symm (eq x) ∈ center SL(n,ZMod 2) at hh
    rw [binary_center_eq_bot (by omega : 0 < n),mem_bot] at hh
    exact (eq.trans (slEquivLinear n).symm).map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 3 c.component := by
    rw [primeRank_equiv 3 (eq.trans (slEquivLinear n).symm)]
    exact SmallCubicRank.four_or_five hn
  have ho := (linear_outer_isTwoGroup hn).of_equiv (MulAut.outerCongr eq).symm
  have hlow := r.fixed_three_rank_of_full_component_direct c hI hcard hz hzne hc hr ho a ha
  obtain ⟨_,horder,Q,hQ⟩ := marked_component_twoCentral r hcard c hI hP hz hzne a ha hi
  let b := MulAut.congr eq a
  have hb : orderOf b = 2 := (MulAut.congr eq).orderOf_eq a |>.trans horder
  obtain ⟨t,ht⟩ : ∃ t, b = MulAut.conj t := by
    apply (MulAut.congr_inner_iff eq a).mpr
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,hx.symm⟩
  have htne : t ≠ 1 := by
    intro he
    rw [ht,he,map_one,orderOf_one] at hb
    omega
  let R := Q.mapSurjective (f := eq.toMonoidHom) eq.surjective
  have hRt : ∀ x ∈ R, x*t=t*x := by
    rintro x ⟨y,hy,rfl⟩
    have hh := congrArg eq (hQ ⟨y,hy⟩)
    have hbfix : b (eq y) = eq y := by
      change eq (a (eq.symm (eq y))) = eq y
      rwa [eq.symm_apply_apply]
    rw [ht] at hbfix
    exact (mul_inv_eq_iff_eq_mul.mp hbfix).symm
  have hu := binary_fixed_rank hn t htne R hRt
  rw [←ht,←primeRank_equiv 3 (MulAut.fixedSubgroupCongr eq a)] at hu
  omega
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
