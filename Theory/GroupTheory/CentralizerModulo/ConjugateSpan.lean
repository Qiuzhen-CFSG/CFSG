module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CentralizerModulo

/-!
# Centralizers of conjugate spans modulo a normal subgroup

The centralizer of the normal closure of A in a quotient is the normal core
of the centralizer of A. We also identify normal closure inside an overgroup
with its embedded conjugate span. These identities retain the relative normal
core and the literal quotient map used in F.8.1(c) and F.8.2(3) of
Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.316.
-/

@[expose] public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Centralizing all conjugates is precisely the normal core of the seed centralizer. -/
theorem centralizerModulo_normalClosure_eq_normalCore (A N : Subgroup G) [N.Normal] :
    centralizerModulo ⊤ (normalClosure (A : Set G)) N =
      (centralizerModulo ⊤ A N).normalCore := by
  let q := QuotientGroup.mk' N
  let C := centralizerModulo ⊤ A N
  have hq := QuotientGroup.mk'_surjective N
  have hnormal : ((normalClosure (A : Set G)).map q).Normal := Normal.map inferInstance q hq
  have hCnormal : (centralizerModulo ⊤ (normalClosure (A : Set G)) N).Normal := by
    unfold centralizerModulo
    infer_instance
  apply le_antisymm
  · apply normal_le_normalCore.mpr
    exact inf_le_inf_left _ (comap_mono (centralizer_le (map_mono le_normalClosure)))
  · have hKnormal : (C.normalCore.map q).Normal := Normal.map inferInstance q hq
    have ha : A.map q ≤ centralizer (C.normalCore.map q : Set (G ⧸ N)) := by
      apply le_centralizer_iff.mp
      rintro _ ⟨c, hc, rfl⟩
      exact (C.normalCore_le hc).2
    have hb : (normalClosure (A : Set G)).map q ≤
        centralizer (C.normalCore.map q : Set (G ⧸ N)) := by
      rw [map_normalClosure _ q hq]
      exact normalClosure_le_normal ha
    intro c hc
    exact ⟨mem_top _, (le_centralizer_iff.mp hb) (mem_map_of_mem q hc)⟩

/-- Relative normal closure and the ambient conjugate span agree under inclusion. -/
theorem normalClosure_subgroupOf_eq_conjugateSpanBy (A H : Subgroup G) (hAH : A ≤ H) :
    normalClosure (A.subgroupOf H : Set H) = (conjugateSpanBy A H).subgroupOf H := by
  let U := conjugateSpanBy A H
  let : (U.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy A H)
  apply le_antisymm
  · exact normalClosure_le_normal (fun x hx => le_conjugateSpanBy _ _ hx)
  · let C := normalClosure (A.subgroupOf H : Set H)
    have hA : A ≤ C.map H.subtype := by
      intro a ha
      exact ⟨⟨a, hAH ha⟩, le_normalClosure ha, rfl⟩
    have hn : H ≤ normalizer (C.map H.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      rintro g hg _ ⟨x, hx, rfl⟩
      exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, (inferInstance : C.Normal).conj_mem x hx ⟨g, hg⟩, rfl⟩
    intro u hu
    obtain ⟨c, hc, he⟩ := conjugateSpanBy_le hA hn hu
    exact H.subtype_injective he ▸ hc

/-- The identity with the literal ambient conjugate span, inside H. -/
theorem centralizerModulo_conjugateSpanBy_eq_normalCore
    (A H N : Subgroup G) (hAH : A ≤ H) [(N.subgroupOf H).Normal] :
    centralizerModulo ⊤ ((conjugateSpanBy A H).subgroupOf H) (N.subgroupOf H) =
      (centralizerModulo ⊤ (A.subgroupOf H) (N.subgroupOf H)).normalCore := by
  rw [← normalClosure_subgroupOf_eq_conjugateSpanBy A H hAH,
    centralizerModulo_normalClosure_eq_normalCore]

end Subgroup
