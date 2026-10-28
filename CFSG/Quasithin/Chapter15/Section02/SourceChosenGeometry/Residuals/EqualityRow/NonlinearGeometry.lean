module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.BinaryG2Exclusion
public import Theory.GroupTheory.PrimeRankNormalIntersection

/-!
# Original residual geometry for the nonlinear component rows

The actual wreath residual has three-rank two, so its intersection with a
normalized subgroup of an escaping overgroup has order divisible by three
whenever that subgroup does.  The same original wreath quotient makes H
solvable.  The plane Sylow subgroup restricts along subnormality to a full
Sylow subgroup of each component.  These are the geometric inputs to the
nonbinary G₂, symplectic and triple-six contradictions, with the literal
offender plane retained and without a partner-residual identity.

Source: Aschbacher--Smith, proof of 15.2.23, printed pp.1116--1117,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- Three-rank two forces a cubic intersection with a normalized subgroup
of the actual escaping overgroup. -/
theorem ResidualInput.residual_intersection_three_dvd
    (r : ResidualInput h H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) {A : Subgroup G} (hAI : A ≤ I)
    (hKA : residual H ≤ normalizer (A : Set G))
    (hthree : 3 ∣ Nat.card A) :
    3 ∣ Nat.card (residual H ⊓ A : Subgroup G) := by
  let K := residual H
  have hKI : K ≤ I :=
    (le_sup_left.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hE
  let EI := E.map (inclusion hKI)
  let e : E ≃* EI := E.equivMapOfInjective (inclusion hKI) (inclusion_injective hKI)
  let : IsElementaryAbelian 3 EI := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hEI : Nat.card EI = 3 ^ 2 := by
    rw [←Nat.card_congr e.toEquiv,hcard,r.residual_rank_two]
  have hnorm : EI ≤ normalizer (A.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hAI]
    rintro _ ⟨x,hx,rfl⟩
    exact hKA x.property
  have hAIcard : 3 ∣ Nat.card (A.subgroupOf I) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv]
    exact hthree
  have hr : primeRank 3 I ≤ 2 :=
    (Chapter1.RadicalExclusions.sqtk_of_mem_H h.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hne := Subgroup.inf_ne_bot_of_elementary_plane EI (A.subgroupOf I)
    hnorm hAIcard hEI hr
  have hp : IsPGroup 3 (EI ⊓ A.subgroupOf I : Subgroup I) :=
    (IsElementaryAbelian.isPGroup 3 EI).to_le inf_le_left
  have hd : 3 ∣ Nat.card (EI ⊓ A.subgroupOf I : Subgroup I) := by
    rcases hp.card_eq_or_dvd with hh | hh
    · exact (hne (card_eq_one.mp hh)).elim
    · exact hh
  let j : (EI ⊓ A.subgroupOf I : Subgroup I) →* (K ⊓ A : Subgroup G) := {
    toFun := fun x => ⟨x.val.val, by
      obtain ⟨k,hk,he⟩ := x.property.1
      exact ⟨(congrArg Subtype.val he) ▸ k.property,x.property.2⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (K ⊓ A : Subgroup G) => (z : G)) hh
  exact hd.trans (card_dvd_of_injective j hj)

/-- The original outside group is solvable, from its literal wreath quotient. -/
theorem ResidualInput.local_solvable (r : ResidualInput h H B) : Group.IsSolvable H := by
  obtain ⟨e⟩ := r.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk',range_subtype])

/-- The original plane Sylow restricts to a full Sylow subgroup of a component. -/
theorem ResidualInput.component_sylow_in_plane
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ (planeCentralizer T ⁅V,B⁆).subgroupOf X := by
  obtain ⟨R,hR⟩ := r.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro x ⟨y,hy,rfl⟩
  have hyR : (y : I) ∈ R := by
    change y ∈ (R : Subgroup I).subgroupOf (X.subgroupOf I)
    rwa [←hQ]
  exact hR ▸ mem_map_of_mem I.subtype hyR

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
