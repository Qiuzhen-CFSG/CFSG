module

public import Theory.GroupTheory.PerfectSimpleImageKernel
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.RankTwoDisjointAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The cubic rank obstruction for an actual perfect A5 residual image

A nontrivial image of a perfect finite group with A5 two-core quotient
retains that quotient. Its order is divisible by three and its center is
contained in its two-core. An elementary subgroup of order nine that
centralizes this image therefore meets it trivially. The rank-two
disjoint-plane theorem then contradicts the image's cubic divisor.

The statement applies to the literal common HS residual or its native
model and to any actual homomorphism. It needs no ambient component
classification, quasisimplicity or nonsingular-centralizer control.

Source: the original common-residual comparison in Section12.6 and the
rank-two disjoint-plane argument of Aschbacher--Smith A.1.27.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualRank

private theorem five_quotient_center_le_core
    {B : Type*} [Group B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    center B ≤ pCore 2 B := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  intro x hx
  have hc : q x ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨b,rfl⟩ := hq y
    simpa only [map_mul] using congrArg q ((mem_center_iff.mp hx) b)
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc
  apply (QuotientGroup.eq_one_iff x).mp
  exact e.map_eq_one_iff.mp hc

private theorem five_quotient_three_dvd_card
    {B : Type*} [Group B] [Finite B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    3 ∣ Nat.card B := by
  have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd := (pCore 2 B).card_quotient_dvd_card
  rw [hc] at hd
  exact (by decide : 3 ∣ 60).trans hd

/-- Every nontrivial perfect image retains the actual A5 two-core quotient,
has three-divisible order, and has its whole center in the two-core. -/
theorem nontrivial_perfect_image_five_quotient
    {J A : Type*} [Group J] [Finite J] [Group.IsPerfect J] [Group A]
    (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (f : J →* A) (hf : f.range ≠ ⊥) :
    Nonempty ((f.range ⧸ pCore 2 f.range) ≃* alternatingGroup (Fin 5)) ∧
      3 ∣ Nat.card f.range ∧ center f.range ≤ pCore 2 f.range := by
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hq2 : IsPGroup 2 q.ker := by rw [hqker]; exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hq2.isNilpotent
  have hf1 : f ≠ 1 := by
    intro hh
    apply hf
    simp only [hh,MonoidHom.range_one]
  have hk := ker_le_of_nontrivial_hom_of_simple_quotient q hq f hf1
  have hk2 : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hq2.to_le hk
  let d := (f.rangeRestrict.quotientPCoreEquivOfSurjective
    f.rangeRestrict_surjective hk2).symm.trans e
  exact ⟨⟨d⟩,five_quotient_three_dvd_card d,five_quotient_center_le_core d⟩

/-- In ambient three-rank at most two, an elementary subgroup of order nine
cannot centralize a nontrivial perfect image of a two-by-A5 group. -/
theorem perfect_five_image_not_centralized_by_plane
    {J A : Type*} [Group J] [Finite J] [Group.IsPerfect J] [Group A] [Finite A]
    (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (f : J →* A) (hf : f.range ≠ ⊥)
    (P : Subgroup A) [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hr : primeRank 3 A ≤ 2) :
    ¬ P ≤ centralizer (f.range : Set A) := by
  intro hc
  obtain ⟨_,hthree,hcenter⟩ := nontrivial_perfect_image_five_quotient e f hf
  have hd : Disjoint P f.range := by
    apply disjoint_def.mpr
    intro x hxP hxB
    let b : f.range := ⟨x,hxB⟩
    have hb : b ∈ center f.range := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hc hxP y y.property)
    have hxQ : x ∈ (pCore 2 f.range).map f.range.subtype :=
      mem_map_of_mem f.range.subtype (hcenter hb)
    exact disjoint_def.mp ((IsElementaryAbelian.isPGroup 3 P).disjoint_of_coprime
      (pCore_isPGroup.map f.range.subtype) (by decide)) hxP hxQ
  have hcop := coprime_card_of_normalized_disjoint_plane hr P f.range hP
    (hc.trans (Subgroup.centralizer_le_normalizer _)) hd
  exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp hcop hthree

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualRank
