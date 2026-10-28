module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.ThreeSourceReduction

/-!
# The dimension-three source endpoint with two explicit prerequisites

The original simplicity and nonabelianness exclude the normal elementary-eight
alternative of I.4.6. The nonnormal quaternion reduction leaves A₈ or A₉;
the actual exceptional isomorphism converts A₈ to PSL₄(2). Both resulting
12.2.13 alternatives retain the original block marking.

The affine point-centralizer calculation must still supply the local I.4.6
hypotheses and quaternion nonnormality inside C_G(z). The A₃ incidence geometry
must also be constructed. These conditional applications do not assert that
12.2.27(2) is proved before both inputs are discharged.
Source: Aschbacher–Smith 12.2.27(2), p.807, and I.4.6, p.417.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
open Extraspecial32 Extraspecial32.NonnormalRecognition
open Quasithin.I5
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Simplicity and nonabelianness in the original source hypotheses exclude
the normal elementary-eight alternative of I.4.6. -/
theorem not_elementaryEight {K : GroupClass.{u}} (h : Hypothesis1223 K T L) :
    ¬ ElementaryEightAlternative G := by
  let := h.simpleQTKE.simple
  rintro ⟨E, hn, he, hc, _⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · rw [hb, card_bot] at hc
    norm_num at hc
  · let := he
    apply h.simpleQTKE.nonabelian
    refine ⟨⟨?_⟩⟩
    intro a b
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨a, ht.symm ▸ mem_top a⟩ : E) ⟨b, ht.symm ▸ mem_top b⟩)

/-- The exact source alternatives from the two still missing producers.
The local producer must calculate I.4.6 and nonnormality inside C_G(z);
the geometry producer must prove actual incidence on the constructed cosets. -/
theorem source_recognition_of_local_geometry {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L)
    (localData : ∃ z : G, Nonempty (Hypotheses z) ∧ QuaternionSubgroupsNonnormal z)
    (geometry : ∀ (M : Subgroup G) (S : DSystem .A3 M), S.Q 0 ≠ ⊥ →
      Nonempty (A3Recognition.GeometryData S)) :
    ClassicalGroup.IsPSL G 4 2 ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  obtain ⟨z, ⟨hz⟩, hn⟩ := localData
  rcases nonnormal_recognition_of_geometry hz hn geometry with he | he | ha
  · exact (not_elementaryEight h he).elim
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
      ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
  · exact Or.inr ha

theorem recognizedGroup_of_local_geometry {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L)
    (localData : ∃ z : G, Nonempty (Hypotheses z) ∧ QuaternionSubgroupsNonnormal z)
    (geometry : ∀ (M : Subgroup G) (S : DSystem .A3 M), S.Q 0 ≠ ⊥ →
      Nonempty (A3Recognition.GeometryData S)) : RecognizedGroup G 3 := by
  rcases source_recognition_of_local_geometry h localData geometry with hp | ha
  · exact Or.inl hp
  · exact Or.inr (Or.inl ⟨rfl, ha⟩)

/-- The original block marking is retained in both surviving alternatives. -/
theorem alternatives_of_local_geometry {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (C : SplitLinearConfiguration L V 3)
    (localData : ∃ z : G, Nonempty (Hypotheses z) ∧ QuaternionSubgroupsNonnormal z)
    (geometry : ∀ (M : Subgroup G) (S : DSystem .A3 M), S.Q 0 ≠ ⊥ →
      Nonempty (A3Recognition.GeometryData S)) : Alternatives12213 T L V := by
  rcases source_recognition_of_local_geometry h localData geometry with hp | ha
  · exact Or.inr (Or.inl ⟨3, Or.inl rfl, C.block, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨C.block, ha⟩))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
