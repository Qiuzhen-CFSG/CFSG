module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.Heptad
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Excluding normal A5 blocks in simple local quotients

For a normal subgroup A, the image in G/O2(G) is exactly A/O2(A).
If the ambient quotient is simple, this image is trivial or the whole
quotient. An alternating-five block has quotient order 60, so both cases
are impossible when the ambient simple group has another order.
The literal M23 heptad application uses its constructed A7 quotient.
Source: Aschbacher–Smith C.3.1(4), printed pp.149–151, and H.14.2(3), p.397.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem not_alternatingFive_of_simple_core_quotient
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : (G ⧸ pCore 2 G) ≃* S) (hc : Nat.card S ≠ 60)
    (A : Subgroup G) [A.Normal] (hA : IsAlternatingBlock A 5) : False := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := A.map q
  let I := B.map e.toMonoidHom
  let eB := (inferInstance : A.Normal).isSubnormal.quotientCoreImageEquiv 2
  let eI : (A ⧸ pCore 2 A) ≃* I := eB.trans (e.subgroupMap B)
  obtain ⟨eA⟩ := hA.2.2.quotient_iso
  have hcard : Nat.card I = 60 := by
    rw [← Nat.card_congr eI.toEquiv, Nat.card_congr eA.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  have hB : B.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hI : I.Normal := Subgroup.Normal.map hB e.toMonoidHom e.surjective
  rcases hI.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.card_bot] at hcard
    contradiction
  · rw [h, Subgroup.card_top] at hcard
    exact hc hcard

theorem native_heptad_no_normal_alternatingFive
    (A : Subgroup Sporadic.Mathieu.M23Geometry.CommonFour.markedHeptadStabilizer)
    [A.Normal] : ¬ IsAlternatingBlock A 5 := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  apply not_alternatingFive_of_simple_core_quotient
    Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.sourceQuotientEquiv
  rw [nat_card_alternatingGroup]
  norm_num
end CFSG.Quasithin.ChapterC
