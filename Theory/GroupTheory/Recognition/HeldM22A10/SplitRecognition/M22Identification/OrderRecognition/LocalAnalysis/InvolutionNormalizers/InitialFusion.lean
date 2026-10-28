module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.NonWeakClosure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.ActorFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.VectorFusion

/-!
# Assembly of Janko's initial involution fusion

Non-weak-closure supplies fusion with one of the four noncentral local
representatives. Lemma 3 sends the actor `a` branch to the `d` branch;
Lemma 2 then fuses the nonidentity elements of F. Lemma 4 handles the
`z 1` branch by fusing E. Both routes reach printed `z₃`, our `z 2`.

The final assembly discharges Lemmas 3 and 4 with their proved ambient
normalizer arguments. Its sole additional premise is the conditional
Lemma 2 input: fusion with `d` supplies the actual F-normalizer action.
The parent involution-normalizer theorem must construct that input.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemmas 2–5, p.5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The transitive action on F includes fusion with printed `z₃`. -/
public theorem z_two_fusion_of_FNormalizerAction (hF : FNormalizerAction D k) :
    IsConj D.z (CaseII.into D k (CaseII.z 2)) := by
  have hmem (v : TwistedModel) (hv : v ∈ CaseII.modelF) :
      CaseII.into D k v ∈ CaseII.F D k := by
    rw [← CaseII.modelF_map D k]
    exact mem_map_of_mem _ hv
  let x : CaseII.F D k :=
    ⟨CaseII.into D k (CaseII.z 0), hmem _ CaseII.modelF_generators.1⟩
  let y : CaseII.F D k :=
    ⟨CaseII.into D k (CaseII.z 2), hmem _ CaseII.modelF_generators.2.1⟩
  have hne (v : TwistedModel) (hv : orderOf v = 2) : CaseII.into D k v ≠ 1 := by
    intro he
    have hv1 : v = 1 := CaseII.into_injective D k (he.trans (map_one _).symm)
    simp [hv1] at hv
  obtain ⟨g, hg⟩ := hF.fusion x y
    (fun he => hne _ (CaseII.z_order 0) (congrArg Subtype.val he))
    (fun he => hne _ (CaseII.z_order 2) (congrArg Subtype.val he))
  rw [← CaseII.into_z_zero D k]
  exact isConj_iff.mpr ⟨g, hg⟩

/-- Conditional assembly of Lemma 5. The final theorem below discharges
`h3` and `h4` with Lemmas 3 and 4; `hF` is the retained Lemma 2 input. -/
public theorem initial_fusion_of_lemma3_lemma4 [IsSimpleGroup G]
    (hF : IsConj D.z (CaseII.into D k CaseII.d) → FNormalizerAction D k)
    (h3 : IsConj D.z (CaseII.into D k CaseII.a) →
      IsConj D.z (CaseII.into D k CaseII.d))
    (h4 : IsConj D.z (CaseII.into D k (CaseII.z 1)) →
      ∀ x y : CaseII.E D k, x ≠ 1 → y ≠ 1 → IsConj (x : G) (y : G)) :
    IsConj D.z (CaseII.into D k (CaseII.z 2)) := by
  rcases CaseII.initial_fusion_alternatives D k with h | h | h | h
  · have hmem (i : Fin 4) : CaseII.into D k (CaseII.z i) ∈ CaseII.E D k := by
      rw [← CaseII.modelE_map D k]
      exact mem_map_of_mem _ (CaseII.z_mem_modelE i)
    let x : CaseII.E D k := ⟨CaseII.into D k (CaseII.z 0), hmem 0⟩
    let y : CaseII.E D k := ⟨CaseII.into D k (CaseII.z 2), hmem 2⟩
    have hne (i : Fin 4) : (⟨CaseII.into D k (CaseII.z i), hmem i⟩ : CaseII.E D k) ≠ 1 := by
      intro he
      have hv : CaseII.z i = 1 := CaseII.into_injective D k
        ((congrArg Subtype.val he).trans (map_one _).symm)
      have ho := CaseII.z_order i
      simp [hv] at ho
    simpa only [x, y, CaseII.into_z_zero D k] using h4 h x y (hne 0) (hne 2)
  · exact h
  · exact z_two_fusion_of_FNormalizerAction D k (hF (h3 h))
  · exact z_two_fusion_of_FNormalizerAction D k (hF h)

/-- Janko's initial fusion (Lemma 5), with only the conditional Lemma 2
input retained. Non-weak-closure and the proved Lemmas 3 and 4 force the
marked involution to fuse with printed `z₃`, our `CaseII.z 2`. -/
public theorem initial_fusion_of_caseII [IsSimpleGroup G]
    (hF : IsConj D.z (CaseII.into D k CaseII.d) → FNormalizerAction D k) :
    IsConj D.z (CaseII.into D k (CaseII.z 2)) :=
  initial_fusion_of_lemma3_lemma4 D k hF
    (actor_fusion_of_a D k) (elementary_fusion_of_z_one_fusion D k)

end Theory.GroupTheory.HeldM22A10.M22Identification
