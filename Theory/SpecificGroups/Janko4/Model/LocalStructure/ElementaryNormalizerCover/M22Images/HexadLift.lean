module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ExactImages
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadKernels

/-!
# The first M22 lift is the native octad pullback

The original second-centralizer residual embeds in the Mathieu local. Its
M22 quotient agrees with the original Mathieu quotient after the actual
pair-marking conjugation. The native hexad-kernel comparison and octad
transitivity therefore put its first E16 inverse image into the fixed octad
pullback Q. Both have order 32768, giving equality with the literal conjugate.

The final consumer replaces the first inverse-image container in the mixed
zero-form reduction by the very Q used by the native F geometry. The other
E16 and E8 lifts retain their kernel-intersection and normalizer obligations.
This is a subgroup-placement result; it does not assert that N(X) lies in Q.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.2.1
and Proposition 2.2.2(i)--(ii), pp.489--490. The native Mathieu, pair and kernel
markings, with their source attribution, are those of the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped Pointwise
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open Janko4.InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf M22ChapterH
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- The residual inclusion, factored through the literal Mathieu local. -/
@[expose] def residualToMathieu : residual →* max1 :=
  localCentralizer.subtype.comp (ambientEquivLocal.toMonoidHom.comp residual.subtype)

theorem residualToMathieu_val (r : residual) :
    (residualToMathieu r : Model) = residualInclusion r := by
  have h := ambientEquivLocal_symm_val (ambientEquivLocal r.val)
  rw [ambientEquivLocal.symm_apply_apply] at h
  exact h.symm

/-- The inner M22 quotient and the original Mathieu quotient agree through
 the actual pair-marking conjugator. -/
theorem residualProjection_mathieu (r : residual) :
    m22Embedding (residualProjection r) =
      pairMover * LinearFive.projection (residualToMathieu r) * pairMover⁻¹ := by
  have he : m22ToPairStabilizer (residualProjection r) =
      starPairEquivNative (toStarPair (ambientEquivLocal r.val)) := by
    apply m22PairStabilizerEquivAut.injective
    rw [m22PairStabilizerEquivAut_inner,residualProjection_action]
    rfl
  have hv := congrArg (fun x : MathieuCode.m22PairStabilizer => (x : M24)) he
  exact hv

private theorem pointwise_conjugate_le (O P : M24LocalGeometry.Octad) (g : M24)
    (hg : g • O.val = P.val) :
    (octadPointwiseKernel O).map (MulAut.conj g).toMonoidHom ≤ octadPointwiseKernel P := by
  rintro _ ⟨u,hu,rfl⟩
  apply (mem_octadPointwiseKernel P _).mpr
  intro i hi
  have hip : i ∈ g • O.val := hg.symm ▸ hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_smul_finset.mp hip
  have huj := (mem_octadPointwiseKernel O u).mp hu j hj
  change (g : Equiv.Perm (Fin 24))
    ((u : Equiv.Perm (Fin 24)) ((g : Equiv.Perm (Fin 24)).symm
      ((g : Equiv.Perm (Fin 24)) j))) = (g : Equiv.Perm (Fin 24)) j
  rw [Equiv.symm_apply_apply]
  exact congrArg (fun k => (g : Equiv.Perm (Fin 24)) k) huj

/-- The first M22 image lift is carried into the original pointwise octad
pullback Q by a literal element of max1. -/
theorem hexadLift_conjugate_le_Q :
    ∃ s : max1, (residualLift (m22InnerHexadKernel m22SourceOctad)).map
      (MulAut.conj (s : Model)).toMonoidHom ≤ LinearFive.Q := by
  obtain ⟨u,hu⟩ := M24LocalGeometry.exists_smul_octad_eq m22SourceOctad LinearFive.O
  obtain ⟨s,hs⟩ := MathieuHallActors.projection_surjective (u*pairMover)
  refine ⟨s,?_⟩
  rintro _ ⟨_,⟨r,hr,rfl⟩,rfl⟩
  refine ⟨s * residualToMathieu r * s⁻¹,?_,?_⟩
  · change LinearFive.projection (s * residualToMathieu r * s⁻¹) ∈ LinearFive.A
    rw [map_mul,map_mul,map_inv,hs]
    have hm : m22Embedding (residualProjection r) ∈ octadPointwiseKernel m22SourceOctad := by
      rw [← Hexad.inner_kernel_image]
      exact mem_map_of_mem m22Embedding hr
    have hh := pointwise_conjugate_le m22SourceOctad LinearFive.O u hu
      (mem_map_of_mem (MulAut.conj u).toMonoidHom hm)
    change u*m22Embedding (residualProjection r)*u⁻¹ ∈ LinearFive.A at hh
    rw [residualProjection_mathieu] at hh
    simpa only [mul_inv_rev, mul_assoc] using hh
  · change (s : Model) * (residualToMathieu r : Model) * (s : Model)⁻¹ = _
    rw [residualToMathieu_val]
    rfl


private theorem card_comap_surjective {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Surjective f) (B : Subgroup H) :
    Nat.card (B.comap f) = Nat.card B * Nat.card f.ker := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero B.index_ne_zero_of_finite)
  calc
    Nat.card (B.comap f) * B.index = Nat.card G := by
      rw [← B.index_comap_of_surjective hf]
      exact (B.comap f).card_mul_index
    _ = (Nat.card B * Nat.card f.ker) * B.index := by
      have hc := f.ker.index_mul_card
      rw [index_ker,MonoidHom.range_eq_top_of_surjective f hf,card_top] at hc
      rw [← hc,← B.card_mul_index]
      ac_rfl

/-- The literal inverse image has the full original E2048 kernel. -/
theorem residualLift_card (B : Subgroup M22) :
    Nat.card (residualLift B) = Nat.card B * 2048 := by
  rw [residualLift,card_map_of_injective residualInclusion_injective,
    card_comap_surjective residualProjection residualProjection_surjective]
  have hk : Nat.card residualProjection.ker = 2048 := by
    rw [← card_map_of_injective residualInclusion_injective,residualProjection_kernel_image]
    change Nat.card ((Cardinality.localKernel matrixA_mul_self matrixB_pow_four).map max1.subtype) = 2048
    rw [card_map_of_injective max1.subtype_injective,Cardinality.localKernel_card]
  rw [hk]

private theorem octadPullback_card : Nat.card LinearFive.Q = 32768 := by
  rw [LinearFive.Q,card_map_of_injective max1.subtype_injective,
    card_comap_surjective LinearFive.projection MathieuHallActors.projection_surjective,
    LinearFive.A_card,MathieuHallActors.projection_ker,Cardinality.localKernel_card]

/-- The first lifted E16 is exactly a conjugate of the native octad pullback,
not merely an abstract group with the same order. -/
theorem hexadLift_conjugate_eq_Q :
    ∃ s : max1, (residualLift (m22InnerHexadKernel m22SourceOctad)).map
      (MulAut.conj (s : Model)).toMonoidHom = LinearFive.Q := by
  obtain ⟨s,hs⟩ := hexadLift_conjugate_le_Q
  refine ⟨s,eq_of_le_of_card_ge hs ?_⟩
  rw [card_map_of_injective (MulAut.conj (s : Model)).injective,residualLift_card,
    Hexad.inner_kernel_card,octadPullback_card]

/-- The same equality oriented for the literal normalizer-cover containers. -/
theorem hexadLift_eq_Q_conjugate : ∃ s : max1,
    residualLift (m22InnerHexadKernel m22SourceOctad) =
      LinearFive.Q.map (MulAut.conj (s : Model)).toMonoidHom := by
  obtain ⟨s,hs⟩ := hexadLift_conjugate_eq_Q
  refine ⟨s⁻¹,?_⟩
  rw [← hs,map_map]
  have he : (MulAut.conj ((s⁻¹ : max1) : Model)).toMonoidHom.comp
      (MulAut.conj (s : Model)).toMonoidHom = MonoidHom.id Model := by
    ext x
    simp [mul_assoc]
  rw [he,map_id]

/-- Actual application to the mixed zero-form source branch: its first
container is the very Q consumed by the native F geometry. The other two
literal residual lifts retain their independent kernel-intersection duties. -/
theorem zero_form_nonpure_octad_cases (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ∃ g : Model,
      X ≤ LinearFive.Q.map (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift (smallContainer 0)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg | hg | hg⟩ := zero_form_nonpure_three_cases X hzero hn
  · obtain ⟨s,hs⟩ := hexadLift_eq_Q_conjugate
    refine ⟨g*(s : Model),Or.inl ?_⟩
    rw [hs,map_map] at hg
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj (s : Model)).toMonoidHom =
        (MulAut.conj (g*(s : Model))).toMonoidHom := by
      ext x
      simp [mul_assoc]
    rwa [he] at hg
  · exact ⟨g,Or.inr (Or.inl hg)⟩
  · exact ⟨g,Or.inr (Or.inr hg)⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
