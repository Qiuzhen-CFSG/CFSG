module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.CentralizerFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.Nonfusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.ActorNeighborhood
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.NormalizerActors
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.ZTwoSylow

/-!
# Actor fusion in Janko's order-168 branch

Assume C(a) ∩ N(E) is a two-group and d is conjugate to a inside N(E).
Under contrary actor nonfusion, local Sylow control and core-free Z-star
put C(a) in C(z); the given normalizer conjugacy then puts C(d) in N(E).
Every involution in C(a) has its full centralizer in N(E), by its local
coordinates. Simplicity supplies a conjugate of z outside N(E). If this
involution were not conjugate to a, their dihedral group would contain
an involution commuting with both, forcing the outside involution back
into N(E). This contradiction proves actor fusion.

This argument replaces the exceptional small-Ree centralizer branch of
the source; no recognition statement for C(z₂) is consumed. The finite
normalizer calculations prove both inputs from |N(E)/E| = 168.
The final theorem discharges them and assumes only this order and the
given fusion of printed z₁ with z₃, besides the ambient local setup.
The proved Sylow description of C(z₂) is re-exported independently.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed pp.6–7. The replacement
uses the elementary dihedral common-involution argument.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy CaseII
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The finite normalizer inputs suffice for ambient actor fusion. -/
public theorem actor_fusion_of_l27_normalizer_inputs [IsSimpleGroup G]
    (hz3 : IsConj D.z (into D k (z 2)))
    (hp : IsPGroup 2 ↥(centralizer ({into D k a} : Set G) ⊓
      normalizer (E D k : Set G)))
    (hda : ∃ n : normalizer (E D k : Set G),
      (n : G) * into D k d * (n : G)⁻¹ = into D k a) :
    IsConj D.z (into D k d) := by
  by_contra hn
  have ha := l27_a_centralizer_le_marked_of_normalizer_two_group D k hz3 hn hp
  have hd := l27_d_centralizer_le_normalizer_of_actor_control D k ha hda
  let N := normalizer (E D k : Set G)
  have hncore : D.z ∉ N.normalCore := by
    rw [normalizer_E_normalCore D k, mem_bot]
    exact D.z_ne_one
  change ¬ ∀ g : G, g * D.z * g⁻¹ ∈ N at hncore
  push Not at hncore
  obtain ⟨g, hg⟩ := hncore
  have hgz : orderOf (g * D.z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, D.z_order]
  have ha2 : orderOf (into D k a) = 2 := by
    rw [orderOf_injective (into D k) (into_injective D k)]
    exact actor_orders.1
  have hnag : ¬ IsConj (into D k a) (g * D.z * g⁻¹) := by
    intro h
    exact hn (actor_fusion_of_a D k ((isConj_iff.mpr ⟨g, rfl⟩).trans h.symm))
  obtain ⟨w, _, hw, hwa, hwg⟩ :=
    Theory.GroupTheory.exists_central_involution_of_not_isConj _ _ ha2 hgz hnag
  exact hg (l27_a_involution_centralizers_le_normalizer D k hz3 ha hd w
    (mem_centralizer_singleton_iff.mpr hwa.eq) hw
    (mem_centralizer_singleton_iff.mpr hwg.eq.symm))

/-- In the order-168 branch of Janko's Lemma 6, the marked involution is
conjugate to d. The local normalizer inputs are proved from the quotient
order; no additional actor-fusion or centralizer-recognition premise remains. -/
public theorem actor_fusion_of_168 [IsSimpleGroup G]
    (hz3 : IsConj D.z (into D k (z 2)))
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    IsConj D.z (into D k d) := by
  obtain ⟨hp, hda⟩ := l27_normalizer_actor_inputs D k h168
  exact actor_fusion_of_l27_normalizer_inputs D k hz3 hp hda

end Theory.GroupTheory.HeldM22A10.M22Identification
