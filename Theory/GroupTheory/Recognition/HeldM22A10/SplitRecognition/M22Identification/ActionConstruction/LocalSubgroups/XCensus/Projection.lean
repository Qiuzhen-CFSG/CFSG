module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.DerivedNormalizer


/-!
# A split quotient of the literal derived F-normalizer

Restrict the published normalizer projection to X. Its restriction to the
known S5 complement is an isomorphism, since the complement misses the kernel.
The inverse restricts to a section over A5. Thus the kernel remains the literal
relative subgroup F, with no replacement of its conjugation action.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Section 8, Lemma 17, pp.16--17.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The literal derived normalizer has a split A5 quotient with the actual F kernel. -/
public theorem exists_XSplitProjection (L : LocalAnalysisData D k) :
    ∃ (π : X D k →* alternatingGroup (Fin 5))
      (s : alternatingGroup (Fin 5) →* X D k),
      (∀ a, π (s a) = a) ∧ π.ker = (CaseII.F D k).subgroupOf (X D k) := by
  classical
  let N := normalizer (CaseII.F D k : Set G)
  obtain ⟨w⟩ := exists_intersectionActor D k L
  obtain ⟨f, hf, hker, hcomm⟩ := exists_FNormalizerProjection D k L w
  let j : X D k →* N := inclusion (X_le_normalizer_F D k)
  have hxcomm (x : X D k) : j x ∈ _root_.commutator N := by
    have hx := (X_eq_map_commutator D k).le x.property
    obtain ⟨y, hy, he⟩ := hx
    exact (show y = j x from Subtype.ext he) ▸ hy
  let π : X D k →* alternatingGroup (Fin 5) :=
    (f.comp j).codRestrict _ (fun x => by
      have hx := hxcomm x
      rw [hcomm] at hx
      exact hx)
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_F
  let fK : K →* Equiv.Perm (Fin 5) := f.comp K.subtype
  have hi : Function.Injective fK := by
    apply (MonoidHom.ker_eq_bot_iff fK).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    have hxker : (x : N) ∈ f.ker := hx
    rw [hker] at hxker
    exact Subgroup.disjoint_def.mp hK.disjoint hxker x.property
  let := Fintype.ofFinite K
  have hb : Function.Bijective fK :=
    (Fintype.bijective_iff_injective_and_card fK).mpr
      ⟨hi, Fintype.card_congr eK.toEquiv⟩
  let e := MulEquiv.ofBijective fK hb
  let t : Equiv.Perm (Fin 5) →* N := K.subtype.comp e.symm.toMonoidHom
  have ht (a) : f (t a) = a := e.apply_symm_apply a
  have htX (a : alternatingGroup (Fin 5)) : (t a : G) ∈ X D k := by
    rw [X_eq_map_commutator]
    apply mem_map_of_mem
    rw [hcomm]
    change f (t a) ∈ alternatingGroup (Fin 5)
    rw [ht]
    exact a.property
  let s : alternatingGroup (Fin 5) →* X D k :=
    ((N.subtype.comp t).comp (alternatingGroup (Fin 5)).subtype).codRestrict _ htX
  refine ⟨π, s, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    exact ht a
  · ext x
    change π x = 1 ↔ (x : G) ∈ CaseII.F D k
    rw [Subtype.ext_iff]
    change f (j x) = 1 ↔ j x ∈ (CaseII.F D k).subgroupOf N
    rw [← hker]
    rfl
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
