module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.ThreePairModelSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CompletionCubicGeneration
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.ThreeModels
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalEvaluation

/-!
# Evaluation of the literal amalgam in the original ambient group

The actual ATLAS locals and the original source locals have the same fixed
canonical point, pair, and linear overlap maps. Their inverse markings
therefore give compatible local homomorphisms. The literal twenty-two
relations transfer, and the original completion and cubic normalizer give
surjectivity. No finite bound on the universal presentation is used.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open Sporadic.Janko3.AmalgamPresentation
open Sporadic.Janko3.AmalgamPresentation.ModelCoordinates

private theorem local_pair_generates {M : Type*} [Group M] (g : Fin 6 → M)
    (a b : Fin 6) (k : Fin 3) (ha : localIndex a = k) (hb : localIndex b = k) :
    closure {x : closure ({g a,g b} : Set M) |
      ∃ i, (x : M) = g i ∧ localIndex i = k} = ⊤ := by
  apply top_unique
  rw [←closure_preimage_eq_top ({g a,g b} : Set M)]
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with h | h
  · exact ⟨a,h,ha⟩
  · exact ⟨b,h,hb⟩

private theorem transport_range {M C G : Type*} [Group M] [Group C] [Group G]
    (S : Subgroup G) (e : M ≃* C) (d : S ≃* C) :
    (S.subtype.comp (d.symm.toMonoidHom.comp e.toMonoidHom)).range = S := by
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (d.symm.surjective.comp e.surjective),←MonoidHom.range_eq_map,
    S.range_subtype]

/-- The original literal local geometry constructs an actual six-tuple
satisfying all twenty-two relations, and its evaluation is surjective. -/
theorem literal_presentation_evaluation
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ (g : Fin 6 → G) (hs : Satisfies g), Function.Surjective (evaluation hs) := by
  let L := completion j.range (overlap j)
  let M := normalizer (A : Set G)
  let N := normalizer (zpowers (j cubic) : Set G)
  obtain ⟨K,e₁,e₃,e₂,_hK,hpair₁,_hpair₃,_hkernel,_hKm,hthird,hpoint,_hC₂,
      hpointcompat,hlinearcompat,hpaircompat⟩ :=
    literal_canonical_three_pair_models P hc A C l a hC ha j hj
  obtain ⟨m₁,m₂,m₃,_mpoint,_mpair₁,_mpair₃,_mlinear,_mthird,_mkernel,
      mpointcompat,mlinearcompat,mpaircompat⟩ := exists_canonical_three_local_models
  have h₁₂ (x : Sporadic.Janko3.Model) (hx : x ∈ firstLocalModel)
      (hy : x ∈ secondLocalModel) :
      (e₁.symm (m₁ ⟨x,hx⟩) : G) = (e₂.symm (m₂ ⟨x,hy⟩) : G) := by
    obtain ⟨z,hz₁,hz₂⟩ := mpointcompat ⟨x,⟨hx,hy⟩⟩
    have hz : (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∈
        ((j.range).subgroupOf L).map e₁.toMonoidHom := by
      rw [hpoint]
      exact z.property
    obtain ⟨u,hu,he⟩ := hz
    change e₁ u = (z : Theory.PSL2.BinaryFourFieldExtension.Model) at he
    obtain ⟨w,hw₁,hw₂⟩ := hpointcompat ⟨u,hu⟩
    have hwz : w = z := Subtype.ext (hw₁.symm.trans he)
    calc
      (e₁.symm (m₁ ⟨x,hx⟩) : G) = (u : G) := by
        rw [hz₁,←he,e₁.symm_apply_apply]
      _ = (e₂.symm (m₂ ⟨x,hy⟩) : G) := by
        rw [hz₂,←hwz,←hw₂,e₂.symm_apply_apply]
  have h₁₃ (x : Sporadic.Janko3.Model) (hx : x ∈ firstLocalModel)
      (hy : x ∈ NineCoordinates.thirdLocalModel) :
      (e₁.symm (m₁ ⟨x,hx⟩) : G) = (e₃.symm (m₃ ⟨x,hy⟩) : G) := by
    obtain ⟨z,hz₁,hz₃⟩ := mpaircompat ⟨x,⟨hx,hy⟩⟩
    have hz : (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∈
        ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom := by
      rw [hpair₁]
      exact z.property
    obtain ⟨u,hu,he⟩ := hz
    change e₁ u = (z : Theory.PSL2.BinaryFourFieldExtension.Model) at he
    obtain ⟨w,hw₁,hw₃⟩ := hpaircompat ⟨u,hu⟩
    have hwz : w = z := Subtype.ext (hw₁.symm.trans he)
    calc
      (e₁.symm (m₁ ⟨x,hx⟩) : G) = (u : G) := by
        rw [hz₁,←he,e₁.symm_apply_apply]
      _ = (e₃.symm (m₃ ⟨x,hy⟩) : G) := by
        rw [hz₃,←hwz,←hw₃,e₃.symm_apply_apply]
  have h₂₃ (x : Sporadic.Janko3.Model) (hx : x ∈ secondLocalModel)
      (hy : x ∈ NineCoordinates.thirdLocalModel) :
      (e₂.symm (m₂ ⟨x,hx⟩) : G) = (e₃.symm (m₃ ⟨x,hy⟩) : G) := by
    obtain ⟨z,hz₂,hz₃⟩ := mlinearcompat ⟨x,⟨hx,hy⟩⟩
    have hz : (CubicNormalizerModel.linearThirdEquiv z : CubicNormalizerModel.Model) ∈
        (M.subgroupOf N).map e₃.toMonoidHom := by
      rw [hthird]
      exact (CubicNormalizerModel.linearThirdEquiv z).property
    obtain ⟨u,hu,he⟩ := hz
    change e₃ u = (CubicNormalizerModel.linearThirdEquiv z : CubicNormalizerModel.Model) at he
    obtain ⟨w,hw₂,hw₃⟩ := hlinearcompat ⟨u,⟨hu,u.property⟩⟩
    have hwz : w = z := CubicNormalizerModel.linearThirdEquiv.injective
      (Subtype.ext (hw₃.symm.trans he))
    calc
      (e₂.symm (m₂ ⟨x,hx⟩) : G) = (u : G) := by
        rw [hz₂,←hwz,←hw₂,e₂.symm_apply_apply]
      _ = (e₃.symm (m₃ ⟨x,hy⟩) : G) := by
        rw [hz₃,←he,e₃.symm_apply_apply]
  let locals : Fin 3 → Subgroup Sporadic.Janko3.Model
    | 0 => firstLocalModel
    | 1 => secondLocalModel
    | _ => NineCoordinates.thirdLocalModel
  let f : ∀ i, locals i →* G
    | 0 => L.subtype.comp (e₁.symm.toMonoidHom.comp m₁.toMonoidHom)
    | 1 => M.subtype.comp (e₂.symm.toMonoidHom.comp m₂.toMonoidHom)
    | 2 => N.subtype.comp (e₃.symm.toMonoidHom.comp m₃.toMonoidHom)
  have hg : ∀ i, modelGenerator i ∈ locals (localIndex i) := by
    intro i
    fin_cases i <;> apply Subgroup.subset_closure <;> simp
  have hcompat : ∀ i k (x : Sporadic.Janko3.Model) (hi : x ∈ locals i) (hk : x ∈ locals k),
      f i ⟨x,hi⟩ = f k ⟨x,hk⟩ := by
    intro i k x hi hk
    fin_cases i <;> fin_cases k
    · rfl
    · exact h₁₂ x hi hk
    · exact h₁₃ x hi hk
    · exact (h₁₂ x hk hi).symm
    · rfl
    · exact h₂₃ x hi hk
    · exact (h₁₃ x hk hi).symm
    · exact (h₂₃ x hk hi).symm
    · rfl
  have hlocal : ∀ k, closure {x : locals k |
      ∃ i, (x : Sporadic.Janko3.Model) = modelGenerator i ∧ localIndex i = k} = ⊤ := by
    intro k
    fin_cases k
    · exact local_pair_generates modelGenerator 0 1 0 rfl rfl
    · exact local_pair_generates modelGenerator 2 3 1 rfl rfl
    · exact local_pair_generates modelGenerator 4 5 2 rfl rfl
  have hgen : (⨆ k, (f k).range) = ⊤ := by
    have hL : (f 0).range = L := transport_range L m₁ e₁
    have hN : (f 2).range = N := transport_range N m₃ e₃
    have hLN : L ⊔ N = ⊤ :=
      literal_completion_cubic_normalizer_generate P hc A C a j hj
    apply top_unique
    rw [←hLN]
    apply sup_le
    · rw [←hL]
      exact le_iSup (fun k => (f k).range) 0
    · rw [←hN]
      exact le_iSup (fun k => (f k).range) 2
  exact ⟨_,satisfies_of_compatible_local_maps locals modelGenerator hg modelGenerator_satisfies f hcompat,
    evaluation_surjective_of_compatible_local_maps locals modelGenerator hg
      modelGenerator_satisfies f hcompat hlocal hgen⟩

/-- The literal presentation maps onto the original group; no bound on
its universal carrier is assumed. -/
theorem literal_presentation_surjection
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ φ : Carrier →* G, Function.Surjective φ := by
  obtain ⟨g,hs,honto⟩ := literal_presentation_evaluation P hc A C l a hC ha j hj
  exact ⟨evaluation hs,honto⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
