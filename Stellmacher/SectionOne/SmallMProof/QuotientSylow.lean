module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction
public import Stellmacher.SectionOne.SmallMProof.LocalHypotheses

/-!
# Sylow cardinalities and fixed points in the quotient

The quotient Sylow image has cardinality |S:A|. Fixed-space comparisons identify the quotient action fixed points with ambient fixed points, retaining the exact action instances required by the recursion.

The standing Section 1 hypotheses and subgroup/cardinality conditions are
explicit. This is the recursive proof used for the restricted conclusion
`m(S) ≤ 1`; the unrestricted source-facing theorem is not used.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.17–19,
and its offender application in (1.7).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne.SmallMProof

universe u

open RankOneThreeGroupAssembly

public theorem local_quotient_sylow_exists
    {G : Type u} [Group G] [Finite G]
    (S A : Subgroup G) (hS_elem : IsElementaryAbelian 2 S)
    (hAS : A ≤ S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAS
    ∃ P : Sylow 2 (H ⧸ A_H),
      (P : Subgroup (H ⧸ A_H)) =
        (S.subgroupOf H).map (QuotientGroup.mk' A_H) ∧
      IsElementaryAbelian 2 (P : Subgroup (H ⧸ A_H)) := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAS
  obtain ⟨P_H, hP_H⟩ := local_sylow_exists S A hS_elem
  let P := P_H.mapSurjective (QuotientGroup.mk'_surjective A_H)
  have hP : (P : Subgroup (H ⧸ A_H)) =
      (S.subgroupOf H).map (QuotientGroup.mk' A_H) := by
    rw [Sylow.coe_mapSurjective, hP_H]
  refine ⟨P, hP, ?_⟩
  rw [hP]
  let : IsElementaryAbelian 2 S := hS_elem
  let : IsElementaryAbelian 2 (S.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf (show S ≤ H from le_sup_right)
  exact IsElementaryAbelian.map (QuotientGroup.mk' A_H)

public theorem local_quotient_fixedPoints_eq
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S A : Subgroup G) (hS_elem : IsElementaryAbelian 2 S)
    (hAS : A ≤ S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let S_H := S.subgroupOf H
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAS
    let _ : IsInvariant H V (FixedPoints.subgroup A_H V) :=
      fixedPoints_isInvariant_of_normal A_H
    let Pbar := S_H.map (QuotientGroup.mk' A_H)
    FixedPoints.subgroup Pbar (FixedPoints.subgroup A_H V) =
      FixedPoints.subgroup S_H (FixedPoints.subgroup A_H V) := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let S_H := S.subgroupOf H
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAS
  let : IsInvariant H V (FixedPoints.subgroup A_H V) :=
    fixedPoints_isInvariant_of_normal A_H
  let Pbar := S_H.map (QuotientGroup.mk' A_H)
  ext v
  simp only [FixedPoints.mem_subgroup]
  constructor
  · intro hv s
    let sbar : Pbar := ⟨QuotientGroup.mk' A_H s,
      ⟨s, s.property, rfl⟩⟩
    have := hv sbar
    change (s : H) • v = v
    change (s : H) • v = v at this
    exact this
  · intro hv sbar
    rcases sbar.property with ⟨s, hs, hsq⟩
    let sH : S_H := ⟨s, hs⟩
    have hsv := hv sH
    change (sbar : H ⧸ A_H) • v = v
    rw [← hsq]
    change s • v = v
    change s • v = v at hsv
    exact hsv

public theorem local_fixedPoints_card_eq
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S A : Subgroup G) (hS_elem : IsElementaryAbelian 2 S)
    (hAS : A ≤ S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let S_H := S.subgroupOf H
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAS
    let _ : IsInvariant H V (FixedPoints.subgroup A_H V) :=
      fixedPoints_isInvariant_of_normal A_H
    Nat.card (FixedPoints.subgroup S_H (FixedPoints.subgroup A_H V)) =
      Nat.card (FixedPoints.subgroup S V) := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let S_H := S.subgroupOf H
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAS
  let : IsInvariant H V (FixedPoints.subgroup A_H V) :=
    fixedPoints_isInvariant_of_normal A_H
  let e : FixedPoints.subgroup S_H (FixedPoints.subgroup A_H V) ≃
      FixedPoints.subgroup S V := {
    toFun := fun v => ⟨(v : FixedPoints.subgroup A_H V), by
      rw [FixedPoints.mem_subgroup]
      intro s
      let sH : S_H := ⟨⟨s, (show S ≤ H from le_sup_right) s.property⟩,
        s.property⟩
      have hsv := (FixedPoints.mem_subgroup
        (M := S_H) (a := (v : FixedPoints.subgroup A_H V))).1 v.property sH
      exact congrArg (fun z : FixedPoints.subgroup A_H V => (z : V)) hsv⟩
    invFun := fun v =>
      ⟨⟨(v : V), by
        rw [FixedPoints.mem_subgroup]
        intro a
        have haS : (a : G) ∈ S := hAS a.property
        exact (FixedPoints.mem_subgroup (M := S) (a := (v : V))).1 v.property
          ⟨(a : G), haS⟩⟩, by
        rw [FixedPoints.mem_subgroup]
        intro s
        apply Subtype.ext
        exact (FixedPoints.mem_subgroup (M := S) (a := (v : V))).1 v.property
          ⟨(s : G), s.property⟩⟩
    left_inv := fun v => rfl
    right_inv := fun v => rfl }
  exact Nat.card_congr e

public theorem local_quotient_sylow_card_eq_index
    {G : Type u} [Group G] [Finite G]
    (S A : Subgroup G) (hS_elem : IsElementaryAbelian 2 S)
    (hAS : A ≤ S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let S_H := S.subgroupOf H
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAS
    Nat.card (S_H.map (QuotientGroup.mk' A_H)) = indexWithin S A := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let S_H := S.subgroupOf H
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAS
  have hAHS : A_H ≤ S_H := fun x hx => hAS hx
  have hmap := natCard_map_mk'_eq S_H A_H
  rw [← Subgroup.index_eq_card] at hmap
  have hcardAH : Nat.card A_H = Nat.card A :=
    natCard_subgroupOf_eq A H (hAS.trans (show S ≤ H from le_sup_right))
  have hcardSH : Nat.card S_H = Nat.card S :=
    natCard_subgroupOf_eq S H (show S ≤ H from le_sup_right)
  have hcardAHS : Nat.card (A_H.subgroupOf S_H) = Nat.card A := by
    rw [natCard_subgroupOf_eq A_H S_H hAHS, hcardAH]
  have hcardAS : Nat.card (A.subgroupOf S) = Nat.card A :=
    natCard_subgroupOf_eq A S hAS
  have hmulLocal := Subgroup.index_mul_card (H := A_H.subgroupOf S_H)
  have hmulAmbient := Subgroup.index_mul_card (H := A.subgroupOf S)
  rw [hcardAHS, hcardSH] at hmulLocal
  rw [hcardAS] at hmulAmbient
  have hindexEq : (A_H.subgroupOf S_H).index = (A.subgroupOf S).index := by
    exact Nat.eq_of_mul_eq_mul_right (hcardAH ▸ Nat.card_pos)
      (hmulLocal.trans hmulAmbient.symm)
  exact hmap.trans hindexEq

end Stellmacher.SectionOne.SmallMProof
