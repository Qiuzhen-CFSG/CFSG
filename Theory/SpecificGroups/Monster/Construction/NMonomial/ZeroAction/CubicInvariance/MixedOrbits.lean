module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.CubicInvariance.Marked
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.CubicInvariance.GroupStructure

/-!
# Normalization of supported mixed zero-summand triples

The actual first and second loop generators act on the two tensor summands
through the literal `N1 → C` map. The element
`psi1N (loopInverse d) * psi2N (loopInverse b)` normalizes the first two
loop labels of a mixed triple, retaining the signs. Invariance under `N1`
keeps its cubic coefficient nonzero. The actual spin pairing then forces
the third half-spin vector to be the standard vector up to sign.

The remaining earlier-source premises are precisely the two signed
`q1ImageConjugation` identities of 29.6(1)--(2). The final theorem below
applies them to the model via its given literal inclusion compatibility.
Neither orbit transitivity nor monomiality nor cubic invariance of `N`
is assumed. The unconditional discharge of those conjugation identities
belongs to `OddComparison/LoopConjugation`; until it is imported, these
exports are conditional reductions, not the completed source orbit theorem.

Source: Aschbacher, *Sporadic Groups*, printed pp. 156--158 (PDF 84--85),
29.6(1)--(2), 29.7(3), and the proof of 29.9. Products act by left
composition. The forms and signed vectors retain the source normalization.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance

private theorem delta_form_support {X : Type*} [Fintype X]
    (s : SignedModules.SignedSet X) (x y : X)
    (h : s.form (s.delta x) (s.delta y) ≠ 0) :
    s.delta y = s.delta x ∨ s.delta y = -s.delta x := by
  rw [s.form_delta, s.delta_apply] at h
  by_cases hxy : x = y
  · exact Or.inl (congrArg s.delta hxy.symm)
  · have hflip : x = s.flip y := by
      by_contra hn
      exact h (by simp [hxy, hn])
    right
    rw [hflip, s.delta_flip, neg_neg]

theorem delta3_of_nonzero_standard_pairing (b : ParkerLoop)
    (h : thirdAxisDomain.form (delta3 loopOne) (delta3 b) ≠ 0) :
    delta3 b = delta3 loopOne ∨ delta3 b = -delta3 loopOne :=
  delta_form_support thirdAxisDomain.signedOrbits _ _ h

theorem mixed_standard_support (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (z x y : Omega) (f : ParkerLoop)
    (h : modelBeta e (modelOdd z loopOne) (modelTwo (pointVector x) (delta2 loopOne))
      (modelThree (pointVector y) (delta3 f)) ≠ 0) :
    delta3 f = delta3 loopOne ∨ delta3 f = -delta3 loopOne := by
  rw [modelBeta_inclusion, modelInclusion_odd e he, modelInclusion_two,
    modelInclusion_three, griessBeta_odd_two_three, oddSpin_one,
    ← spinRestriction_isometry] at h
  simp only [spinRestriction.apply_symm_apply, map_zero, zero_add] at h
  exact delta3_of_nonzero_standard_pairing f (fun hf => h (by rw [hf, mul_zero]))

private theorem spin_two (g : N1) (b c : ParkerLoop)
    (h : g.val.val (axis2 b) = axis2 c) :
    SpinAction.representation g (spinRestriction.symm (delta2 b,0)) =
      spinRestriction.symm (delta2 c,0) := by
  rw [← SpinDirectSum.restriction_vector2 b, spinRestriction.symm_apply_apply]
  rw [show SpinAction.representation g (bothAxesDomain.vector ⟨axis2 b, Or.inl ⟨b,rfl⟩⟩) = _ from
    SpinAction.representation_vector g ⟨axis2 b, Or.inl ⟨b,rfl⟩⟩]
  have hh : (⟨g.val.val (axis2 b), N1_mapsTo_A g.val g.prop (Or.inl ⟨b,rfl⟩)⟩ : A) = ⟨axis2 c, Or.inl ⟨c,rfl⟩⟩ := Subtype.ext h
  refine (congrArg bothAxesDomain.vector hh).trans ?_
  apply spinRestriction.injective
  rw [spinRestriction.apply_symm_apply]
  exact SpinDirectSum.restriction_vector2 c

private theorem spin_three (g : N1) (b c : ParkerLoop)
    (h : g.val.val (axis3 b) = axis3 c) :
    SpinAction.representation g (spinRestriction.symm (0,delta3 b)) =
      spinRestriction.symm (0,delta3 c) := by
  rw [← SpinDirectSum.restriction_vector3 b, spinRestriction.symm_apply_apply]
  rw [show SpinAction.representation g (bothAxesDomain.vector ⟨axis3 b, Or.inr ⟨b,rfl⟩⟩) = _ from
    SpinAction.representation_vector g ⟨axis3 b, Or.inr ⟨b,rfl⟩⟩]
  have hh : (⟨g.val.val (axis3 b), N1_mapsTo_A g.val g.prop (Or.inr ⟨b,rfl⟩)⟩ : A) = ⟨axis3 c, Or.inr ⟨c,rfl⟩⟩ := Subtype.ext h
  refine (congrArg bothAxesDomain.vector hh).trans ?_
  apply spinRestriction.injective
  rw [spinRestriction.apply_symm_apply]
  exact SpinDirectSum.restriction_vector3 c

private theorem leech_one (d : ParkerLoop) :
    n1LeechRepresentation ⟨psi1N d, psi1N_mem_N1 d⟩ = 1 :=
  n1LeechRepresentation_of_mem_Q1 _ (Subgroup.subset_closure (Or.inl ⟨d,rfl⟩))

private theorem leech_two (d : ParkerLoop) :
    n1LeechRepresentation ⟨psi2N d, psi2N_mem_N1 d⟩ = signIsometry d.1 :=
  natural_lift_unique _ _ _ (n1LeechRepresentation_natural _)
    (fun v => (naturalLeechComparison_psi2 d v).symm)

private theorem inclusion_injective (e : oddSpace ≃ₗ[ℝ] TensorTwo) :
    Function.Injective (modelInclusion e) :=
  zeroInclusion_injective.comp (zeroToModel e).symm.injective

private theorem local_two (g : N1) (a a' : NaturalSpace) (b c : ParkerLoop)
    (ha : realLeechRepresentation (n1LeechRepresentation g) a = a')
    (hb : SpinAction.representation g (spinRestriction.symm (delta2 b,0)) =
      spinRestriction.symm (delta2 c,0)) :
    cRepresentation (n1ToC g) (zeroInclusion (zeroTwo a (delta2 b))) =
      zeroInclusion (zeroTwo a' (delta2 c)) := by
  rw [zeroInclusion_two, zeroInclusion_two, cRepresentation_apply]
  change ((realLeechRepresentation (n1LeechRepresentation g) a) ⊗ₜ[ℝ]
      (SpinAction.representation g (spinRestriction.symm (delta2 b,0))),
    cShort (n1ToC g) 0, cSymmetric (n1ToC g) 0) =
      (a' ⊗ₜ[ℝ] spinRestriction.symm (delta2 c,0),0,0)
  rw [ha,hb,map_zero,map_zero]

private theorem local_three (g : N1) (a a' : NaturalSpace) (b c : ParkerLoop)
    (ha : realLeechRepresentation (n1LeechRepresentation g) a = a')
    (hb : SpinAction.representation g (spinRestriction.symm (0,delta3 b)) =
      spinRestriction.symm (0,delta3 c)) :
    cRepresentation (n1ToC g) (zeroInclusion (zeroThree a (delta3 b))) =
      zeroInclusion (zeroThree a' (delta3 c)) := by
  rw [zeroInclusion_three, zeroInclusion_three, cRepresentation_apply]
  change ((realLeechRepresentation (n1LeechRepresentation g) a) ⊗ₜ[ℝ]
      (SpinAction.representation g (spinRestriction.symm (0,delta3 b))),
    cShort (n1ToC g) 0, cSymmetric (n1ToC g) 0) =
      (a' ⊗ₜ[ℝ] spinRestriction.symm (0,delta3 c),0,0)
  rw [ha,hb,map_zero,map_zero]

theorem model_psi1_two (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (d b : ParkerLoop) (x : Omega) :
    ρ (psi1N d) (modelTwo (pointVector x) (delta2 b)) =
      modelTwo (pointVector x) (delta2 (parkerLoopMultiply d b)) := by
  apply inclusion_injective e
  rw [hN1 ⟨psi1N d, psi1N_mem_N1 d⟩, modelInclusion_two, modelInclusion_two]
  apply local_two
  · rw [leech_one, map_one]
    rfl
  · exact spin_two _ _ _ (psi1_axis2 d b)

theorem model_psi1_three (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (d b : ParkerLoop) (x : Omega) :
    ρ (psi1N d) (modelThree (pointVector x) (delta3 b)) =
      modelThree (pointVector x) (delta3 (parkerLoopMultiply b d)) := by
  apply inclusion_injective e
  rw [hN1 ⟨psi1N d, psi1N_mem_N1 d⟩, modelInclusion_three, modelInclusion_three]
  apply local_three
  · rw [leech_one, map_one]
    rfl
  · exact spin_three _ _ _ (psi1_axis3 d b)

theorem model_psi2_two (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (d b : ParkerLoop) (x : Omega) :
    ρ (psi2N d) (modelTwo (pointVector x) (delta2 b)) =
      modelTwo (if d.1.val x = 0 then pointVector x else -pointVector x)
        (delta2 (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) b)) := by
  apply inclusion_injective e
  rw [hN1 ⟨psi2N d, psi2N_mem_N1 d⟩, modelInclusion_two, modelInclusion_two]
  apply local_two
  · rw [leech_two]
    exact realLeechRepresentation_sign_basis d.1 x
  · exact spin_two _ _ _ (psi2_on_axis2 d b)

theorem model_psi2_three (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (d b : ParkerLoop) (x : Omega) :
    ρ (psi2N d) (modelThree (pointVector x) (delta3 b)) =
      modelThree (if d.1.val x = 0 then pointVector x else -pointVector x)
        (delta3 (parkerLoopMultiply d b)) := by
  apply inclusion_injective e
  rw [hN1 ⟨psi2N d, psi2N_mem_N1 d⟩, modelInclusion_three, modelInclusion_three]
  apply local_three
  · rw [leech_two]
    exact realLeechRepresentation_sign_basis d.1 x
  · exact spin_three _ _ _ (psi2_axis3 d b)

private def SignedEq (u v : ModelSpace) : Prop :=
  ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ u = a • v

private theorem sign_mul {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

private theorem SignedEq.refl (v : ModelSpace) : SignedEq v v := ⟨1,Or.inl rfl,by simp⟩

private theorem SignedEq.trans {u v w : ModelSpace} (h : SignedEq u v) (k : SignedEq v w) :
    SignedEq u w := by
  obtain ⟨a,ha,hu⟩ := h
  obtain ⟨b,hb,hv⟩ := k
  exact ⟨a*b,sign_mul ha hb, by rw [hu,hv,smul_smul]⟩

private theorem SignedEq.map (F : Module.End ℝ ModelSpace) {u v : ModelSpace}
    (h : SignedEq u v) : SignedEq (F u) (F v) := by
  obtain ⟨a,ha,hu⟩ := h
  exact ⟨a,ha,by rw [hu,map_smul]⟩

private theorem SignedEq.of_neg (v : ModelSpace) : SignedEq (-v) v :=
  ⟨-1,Or.inr rfl,(neg_one_smul ℝ v).symm⟩

private theorem bit_cases (s : ParkerBit) : s = 0 ∨ s = 1 := by
  have h : ∀ s : ParkerBit, s = 0 ∨ s = 1 := by decide
  exact h s

private theorem signed_odd (s : ParkerBit) (z : Omega) (b : ParkerLoop) :
    SignedEq (modelOdd z (parkerSign s b)) (modelOdd z b) := by
  rcases bit_cases s with rfl | rfl
  · simpa only [parkerSign_zero] using SignedEq.refl (modelOdd z b)
  · have h : modelOdd z (parkerSign 1 b) = -modelOdd z b := by
      simp [modelOdd, TensorProduct.tmul_neg]
    rw [h]
    exact SignedEq.of_neg _

private theorem signed_two (s : ParkerBit) (x : Omega) (b : ParkerLoop)
    (P : Prop) [Decidable P] :
    SignedEq (modelTwo (if P then pointVector x else -pointVector x)
      (delta2 (parkerSign s b))) (modelTwo (pointVector x) (delta2 b)) := by
  have hsign : delta2 (parkerSign s b) = delta2 b ∨
      delta2 (parkerSign s b) = -delta2 b := by
    rcases bit_cases s with rfl | rfl
    · exact Or.inl (congrArg delta2 (parkerSign_zero b))
    · exact Or.inr (delta2_sign b)
  rcases hsign with hs | hs <;> rw [hs] <;> by_cases hP : P
  · simpa only [if_pos hP] using SignedEq.refl (modelTwo (pointVector x) (delta2 b))
  · rw [if_neg hP]
    have hh : modelTwo (-pointVector x) (delta2 b) = -modelTwo (pointVector x) (delta2 b) := by
      simp [modelTwo,TensorProduct.neg_tmul]
    rw [hh]
    exact SignedEq.of_neg _
  · rw [if_pos hP]
    have hh : modelTwo (pointVector x) (-delta2 b) = -modelTwo (pointVector x) (delta2 b) := by
      simp [modelTwo,TensorProduct.tmul_neg]
    rw [hh]
    exact SignedEq.of_neg _
  · rw [if_neg hP]
    have hh : modelTwo (-pointVector x) (-delta2 b) = modelTwo (pointVector x) (delta2 b) := by
      simp [modelTwo,TensorProduct.neg_tmul,TensorProduct.tmul_neg]
    rw [hh]
    exact SignedEq.refl _

private theorem signed_three (x : Omega) (b : ParkerLoop) (P : Prop) [Decidable P] :
    SignedEq (modelThree (if P then pointVector x else -pointVector x) (delta3 b))
      (modelThree (pointVector x) (delta3 b)) := by
  by_cases hP : P
  · simpa only [if_pos hP] using SignedEq.refl (modelThree (pointVector x) (delta3 b))
  · have h : modelThree (-pointVector x) (delta3 b) = -modelThree (pointVector x) (delta3 b) := by
      simp [modelThree, TensorProduct.neg_tmul]
    rw [if_neg hP,h]
    exact SignedEq.of_neg _

/-- Two actual loop generators suffice; multiplication means left composition. -/
def mixedNormalizer (b d : ParkerLoop) : NPlus :=
  ⟨psi1N (loopInverse d) * psi2N (loopInverse b), NPlus.mul_mem
    (Subgroup.subset_closure (Or.inl ⟨loopInverse d,Or.inl rfl⟩))
    (Subgroup.subset_closure (Or.inl ⟨loopInverse b,Or.inr (Or.inl rfl)⟩))⟩

private theorem normalize_labels (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (ho1 : ∀ d z b, ρ (psi1N d) (modelOdd z b) =
      modelOdd z (parkerSign (d.1.val z + golayQuarterWeight d.1 +
        golayHalfOverlap d.1 b.1) b))
    (ho2 : ∀ d z b, ρ (psi2N d) (modelOdd z b) =
      modelOdd z (parkerSign (d.1.val z) (parkerLoopMultiply d b)))
    (z x y : Omega) (b d f : ParkerLoop) :
    SignedEq (ρ (mixedNormalizer b d).val (modelOdd z b)) (modelOdd z loopOne) ∧
    SignedEq (ρ (mixedNormalizer b d).val (modelTwo (pointVector x) (delta2 d)))
      (modelTwo (pointVector x) (delta2 loopOne)) ∧
    SignedEq (ρ (mixedNormalizer b d).val (modelThree (pointVector y) (delta3 f)))
      (modelThree (pointVector y)
        (delta3 (parkerLoopMultiply (parkerLoopMultiply (loopInverse b) f) (loopInverse d)))) := by
  have ho : SignedEq (ρ (psi2N (loopInverse b)) (modelOdd z b)) (modelOdd z loopOne) := by
    rw [ho2,loopInverse_mul]
    exact signed_odd _ _ _
  have ht : SignedEq (ρ (psi2N (loopInverse b)) (modelTwo (pointVector x) (delta2 d)))
      (modelTwo (pointVector x) (delta2 d)) := by
    rw [model_psi2_two e ρ hN1]
    exact signed_two _ _ _ _
  have hh : SignedEq (ρ (psi2N (loopInverse b)) (modelThree (pointVector y) (delta3 f)))
      (modelThree (pointVector y) (delta3 (parkerLoopMultiply (loopInverse b) f))) := by
    rw [model_psi2_three e ρ hN1]
    exact signed_three _ _ _
  change SignedEq ((ρ (_ * _)) _) _ ∧ SignedEq ((ρ (_ * _)) _) _ ∧
    SignedEq ((ρ (_ * _)) _) _
  simp only [map_mul,Module.End.mul_apply]
  refine ⟨(ho.map _).trans ?_, (ht.map _).trans ?_, (hh.map _).trans ?_⟩
  · rw [ho1]
    exact signed_odd _ _ _
  · rw [model_psi1_two e ρ hN1,loopInverse_mul]
    exact SignedEq.refl _
  · rw [model_psi1_three e ρ hN1]
    exact SignedEq.refl _

/-- Normalize a supported mixed triple using the two concrete odd-generator
identities. These identities are the remaining input from 29.6, not an orbit
or coefficient-preservation assumption. -/
theorem mixed_orbit_reduction_of_loop_formulas
    (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (ho1 : ∀ d z b, ρ (psi1N d) (modelOdd z b) =
      modelOdd z (parkerSign (d.1.val z + golayQuarterWeight d.1 +
        golayHalfOverlap d.1 b.1) b))
    (ho2 : ∀ d z b, ρ (psi2N d) (modelOdd z b) =
      modelOdd z (parkerSign (d.1.val z) (parkerLoopMultiply d b)))
    (v : Fin 3 → ModelSpace) (hv : MixedShape v) (hn : tripleValue e v ≠ 0) :
    ∃ h : NPlus, StandardShape (fun i => ρ h.val (v i)) := by
  obtain ⟨z,x,y,b,d,f,p,a,c,t,ha,hc,ht,hp⟩ := hv
  let h := mixedNormalizer b d
  let f' := parkerLoopMultiply (parkerLoopMultiply (loopInverse b) f) (loopInverse d)
  obtain ⟨⟨A,hA,hodd⟩,⟨B,hB,htwo⟩,⟨C,hC,hthree⟩⟩ :=
    normalize_labels e ρ hN1 ho1 ho2 z x y b d f
  have hnon : tripleValue e (fun i => ρ h.val (v i)) ≠ 0 := by
    have hi := modelBeta_n1 e ρ hN1 (HalfActions.inclusion h) (v 0) (v 1) (v 2)
    exact fun hz => hn (hi.symm.trans hz)
  rw [← tripleValue_permute e p] at hnon
  change tripleValue e (fun i => ρ h.val ((v ∘ p) i)) ≠ 0 at hnon
  rw [hp] at hnon
  have hbase : modelBeta e (modelOdd z loopOne)
      (modelTwo (pointVector x) (delta2 loopOne))
      (modelThree (pointVector y) (delta3 f')) ≠ 0 := by
    intro hz
    apply hnon
    change modelBeta e (ρ h.val (a • modelOdd z b))
      (ρ h.val (c • modelTwo (pointVector x) (delta2 d)))
      (ρ h.val (t • modelThree (pointVector y) (delta3 f))) = 0
    dsimp only [h]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [hodd,htwo,hthree]
    dsimp only [f'] at hz
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hz,mul_zero]
  have hs : SignedEq (modelThree (pointVector y) (delta3 f'))
      (modelThree (pointVector y) (delta3 loopOne)) := by
    rcases mixed_standard_support e he z x y f' hbase with hf | hf
    · rw [hf]
      exact SignedEq.refl _
    · rw [hf]
      have hh : modelThree (pointVector y) (-delta3 loopOne) =
          -modelThree (pointVector y) (delta3 loopOne) := by
        simp [modelThree,TensorProduct.tmul_neg]
      rw [hh]
      exact SignedEq.of_neg _
  obtain ⟨D,hD,hfinal⟩ := hs
  refine ⟨h,z,x,y,p,a*A,c*B,t*(C*D),sign_mul ha hA,sign_mul hc hB,
    sign_mul ht (sign_mul hC hD),?_⟩
  change (fun i => ρ h.val ((v ∘ p) i)) = _
  rw [hp]
  funext i
  fin_cases i
  · change ρ h.val (a • modelOdd z b) = (a*A) • modelOdd z loopOne
    rw [map_smul,hodd,smul_smul]
  · change ρ h.val (c • modelTwo (pointVector x) (delta2 d)) =
      (c*B) • modelTwo (pointVector x) (delta2 loopOne)
    rw [map_smul,htwo,smul_smul]
  · change ρ h.val (t • modelThree (pointVector y) (delta3 f)) =
      (t*(C*D)) • modelThree (pointVector y) (delta3 loopOne)
    rw [map_smul,hthree]
    change t • (C • modelThree (pointVector y) (delta3 f')) = _
    rw [hfinal,smul_smul,smul_smul,mul_assoc]

/-- Transfer an actual quotient-conjugation calculation to the specified model
using its literal N1 compatibility. No constructed comparison is imported. -/
theorem model_odd_of_conjugation (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (g : N1) (z y : Omega) (b c : ParkerLoop)
    (hq : q1ImageConjugation g (rOddElement z b) = rOddElement y c) :
    ρ g.val (modelOdd z b) = modelOdd y c := by
  apply inclusion_injective e
  rw [hN1,modelInclusion_odd e he,modelInclusion_odd e he,zeroInclusion_odd,zeroInclusion_odd]
  have hshort : cShortLift (n1ToC g) (rOdd z b) = rOdd y c := by
    apply Subtype.ext
    change cConjugation (pullbackToC (n1Pullback g)) (rOdd z b).val = (rOdd y c).val
    rw [cConjugation_pullback]
    exact hq
  rw [cRepresentation_apply]
  change ((n1ToC g).val 0, cShort (n1ToC g) (shortVector sourceLatticeComparison (rOdd z b)),
    cSymmetric (n1ToC g) 0) = (0,shortVector sourceLatticeComparison (rOdd y c),0)
  rw [map_zero,map_zero,cShort_vector,hshort]

/-- The only earlier-source inputs needed by the orbit reduction are the two
literal signed quotient-conjugation equations of 29.6(1)--(2). -/
theorem mixed_orbit_reduction_of_conjugation
    (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
    (ρ : Representation ℝ N ModelSpace)
    (hN1 : ∀ (g : N1) v, modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v))
    (hq1 : ∀ d z b, q1ImageConjugation ⟨psi1N d,psi1N_mem_N1 d⟩ (rOddElement z b) =
      rOddElement z (parkerSign (d.1.val z + golayQuarterWeight d.1 +
        golayHalfOverlap d.1 b.1) b))
    (hq2 : ∀ d z b, q1ImageConjugation ⟨psi2N d,psi2N_mem_N1 d⟩ (rOddElement z b) =
      rOddElement z (parkerSign (d.1.val z) (parkerLoopMultiply d b)))
    (v : Fin 3 → ModelSpace) (hv : MixedShape v) (hn : tripleValue e v ≠ 0) :
    ∃ h : NPlus, StandardShape (fun i => ρ h.val (v i)) :=
  mixed_orbit_reduction_of_loop_formulas e he ρ hN1
    (fun d z b => model_odd_of_conjugation e he ρ hN1 _ _ _ _ _ (hq1 d z b))
    (fun d z b => model_odd_of_conjugation e he ρ hN1 _ _ _ _ _ (hq2 d z b)) v hv hn

end Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance
