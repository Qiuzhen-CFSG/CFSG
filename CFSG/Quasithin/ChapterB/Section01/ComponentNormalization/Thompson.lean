module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source
public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import Theory.GroupTheory.CComponent.QuasisimpleImage

/-!
# Thompson normalization of surviving C-components

A maximum elementary subgroup has either trivial image on the original normal
binary module or a best-offender image. B.1.5(4) therefore normalizes every
surviving component image. Passing first through the two-core quotient makes
the original C-component an ordinary component. Its nontrivial image reflects
normalization, and the C-component normalizer lifts through the solvable
original two-core.

This applies to the literal local FSU module in the Chapter 10 consumer.
Source: Aschbacher–Smith, B.1.5(4), B.2.5 and 10.1.2(2), printed pp.69, 76, 741.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]

/-- The elementary Thompson subgroup normalizes each C-component that survives
on the original elementary module, when its two-core quotient is quasisimple. -/
theorem thompson_normalizes_surviving_cComponent
    (V S L : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hL : L.IsCComponent)
    (hLq : IsQuasisimple (L ⧸ pCore 2 L))
    (f : H →* Q) (hf : Function.Surjective f)
    (hk : f.ker = centralizer (V : Set H))
    (hc : pCore 2 H ≤ f.ker) (hne : L.map f ≠ ⊥) :
    elementaryAbelianMaxJ S ≤ normalizer (L : Set H) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let fb := QuotientGroup.lift (pCore 2 H) f hc
  have hcomp : fb.comp q = f := by ext; rfl
  have hLnon : L.map q ≠ ⊥ := by
    intro he
    apply hne
    rw [← hcomp, ← map_map, he, Subgroup.map_bot]
  have hLbar : IsComponent (H ⧸ pCore 2 H) (L.map q) :=
    hL.isComponent_map_of_twoCore_killed hLq q (QuotientGroup.mk'_surjective _)
      (by simpa only [q, QuotientGroup.ker_mk'] using pCoreIn_le_of_subnormal 2 hL.subnormal)
      hLnon
  have hLf : IsComponent Q (L.map f) :=
    hL.isComponent_map_of_twoCore_killed hLq f hf
      ((pCoreIn_le_of_subnormal 2 hL.subnormal).trans hc) hne
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  have hreflect (a : H) (ha : f a ∈ normalizer (L.map f : Set Q)) :
      a ∈ normalizer (L : Set H) := by
    rw [← normalizer_cComponent_quotient hL (pCore 2 H)]
    apply hLbar.mem_normalizer_of_mem_normalizer_map fb
    · rwa [map_map, hcomp]
    · rw [map_map, hcomp]
      exact ha
  apply sSup_le
  intro A hA a ha
  apply hreflect a
  by_cases hb : A.map f = ⊥
  · rw [show f a = 1 from (map_eq_bot_iff A).mp hb ha]
    exact one_mem _
  · have hbest := Representation.NormalElementaryQuotient.maxElementary_isBestOffender
      V f hf hk S A hVS hA hb
    exact ChapterB.source_lemma_B_1_5_4
      (Representation.NormalElementaryQuotient.representation V f hf hk)
      (Representation.NormalElementaryQuotient.representation_injective V f hf hk)
      hbest hLf (mem_map_of_mem f ha)
end CFSG.Quasithin.ChapterB
