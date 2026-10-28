module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Actions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Axis2Kernels.Radical

/-!
# Normal-form coordinates of the axis-2 orbit kernels

Evaluate at the loop identity to restrict the first translation to a signed
central element. After removing it, Golay faithfulness modulo the all-ones
line makes the standard automorphism a sign action. Its linearity forces the
half-overlap function to be linear, so the triple-form radical restricts the
second translation to the all-ones line. The automorphism is then trivial.
The parameter `s` records multiplication by Ω or by −Ω throughout.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.3(5–6), printed p. 146.
-/

@[expose] public section

open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

private theorem sign_twice (t : ParkerBit) (b : ParkerLoop) :
    parkerSign t (parkerSign t b) = b := by
  rw [parkerSign_add, CharTwo.add_self_eq_zero, parkerSign_zero]

private theorem signedOmega_commutes (s : ParkerBit) (b : ParkerLoop) :
    parkerLoopMultiply (parkerSign s parkerOmega) b =
      parkerLoopMultiply b (parkerSign s parkerOmega) := by
  rw [parkerLoopMultiply_sign_left, parkerLoopMultiply_sign_right, parkerOmega_commutes]

private theorem signedOmega_twice (s : ParkerBit) (b : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply b (parkerSign s parkerOmega))
      (parkerSign s parkerOmega) = b := by
  simp only [parkerLoopMultiply_sign_right, parkerLoopMultiply_sign_left, sign_twice]
  exact Option.some.inj (rightOmega_rightOmega (some b))

private theorem overlap_right_one (a : golay) : golayHalfOverlap a golayOne = 0 := by
  rw [golayHalfOverlap_symmetric, golayHalfOverlap_one]

private theorem overlap_right_zero (a : golay) : golayHalfOverlap a 0 = 0 := by
  rw [golayHalfOverlap_symmetric, golayHalfOverlap_zero_left]

private theorem overlap_add_one (a b : golay) :
    golayHalfOverlap a (golayOne + b) = golayHalfOverlap a b := by
  rw [golayHalfOverlap_symmetric, golayHalfOverlap_add_left,
    golayHalfOverlap_one, parkerTripleIntersection_one, zero_add, add_zero,
    golayHalfOverlap_symmetric]

private theorem quarterWeight_one : golayQuarterWeight golayOne = 0 := by
  exact congrArg Prod.snd (parkerLoopMultiply_square parkerOmega).symm |>.trans
    (congrArg Prod.snd parkerOmega_square)

private theorem standard_signedOmega (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (s : ParkerBit) :
    α.val (parkerSign s parkerOmega) = parkerSign s parkerOmega := by
  rw [parkerStandard_preserves_sign, hα]

private theorem axis2_initial_coordinate (s : ParkerBit) (d e : ParkerLoop)
    (α : ParkerStandardGroup) (hα : α.val parkerOmega = parkerOmega)
    (h : ∀ b : ParkerLoop,
      α.val (loopSandwich e (parkerLoopMultiply d b)) = b ∨
      α.val (loopSandwich e (parkerLoopMultiply d b)) =
        parkerLoopMultiply b (parkerSign s parkerOmega)) :
    d = parkerSign (golayQuarterWeight e.1) loopOne ∨
      d = parkerSign (golayQuarterWeight e.1) (parkerSign s parkerOmega) := by
  have h0 : loopSandwich e d = loopOne ∨
      loopSandwich e d = parkerSign s parkerOmega := by
    rcases h loopOne with hz | hz
    · left
      apply α.val.injective
      simpa only [loopOne, parkerLoopMultiply_one_right, α.prop.2.1] using hz
    · right
      apply α.val.injective
      simpa only [loopOne, parkerLoopMultiply_one_right, parkerLoopMultiply_one_left,
        standard_signedOmega α hα] using hz
  rw [loopSandwich_sign] at h0
  have hd : d.1 = 0 ∨ d.1 = golayOne := by
    rcases h0 with hz | hz
    · exact Or.inl (congrArg Prod.fst hz)
    · exact Or.inr (congrArg Prod.fst hz)
  have hc : golayHalfOverlap e.1 d.1 = 0 := by
    rcases hd with hd | hd
    · rw [hd, overlap_right_zero]
    · rw [hd, overlap_right_one]
  rw [hc, zero_add] at h0
  rcases h0 with hz | hz
  · left
    exact (sign_twice _ _).symm.trans (congrArg (parkerSign (golayQuarterWeight e.1)) hz)
  · right
    exact (sign_twice _ _).symm.trans (congrArg (parkerSign (golayQuarterWeight e.1)) hz)

private theorem axis2_remove_translation (s : ParkerBit) (d e : ParkerLoop)
    (α : ParkerStandardGroup) (hα : α.val parkerOmega = parkerOmega)
    (h : ∀ b : ParkerLoop,
      α.val (loopSandwich e (parkerLoopMultiply d b)) = b ∨
      α.val (loopSandwich e (parkerLoopMultiply d b)) =
        parkerLoopMultiply b (parkerSign s parkerOmega)) :
    ∀ b : ParkerLoop,
      parkerSign (golayHalfOverlap e.1 b.1) (α.val b) = b ∨
      parkerSign (golayHalfOverlap e.1 b.1) (α.val b) =
        parkerLoopMultiply b (parkerSign s parkerOmega) := by
  have hcancel (c q : ParkerBit) (b : ParkerLoop) :
      parkerSign (c + q) (parkerSign q b) = parkerSign c b := by
    rw [parkerSign_add, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rcases axis2_initial_coordinate s d e α hα h with rfl | rfl
  · intro b
    have hb := h b
    have hf : α.val (loopSandwich e
        (parkerLoopMultiply (parkerSign (golayQuarterWeight e.1) loopOne) b)) =
        parkerSign (golayHalfOverlap e.1 b.1) (α.val b) := by
      rw [parkerLoopMultiply_sign_left, loopOne, parkerLoopMultiply_one_left,
        loopSandwich_sign]
      change α.val (parkerSign (golayHalfOverlap e.1 b.1 + golayQuarterWeight e.1)
        (parkerSign (golayQuarterWeight e.1) b)) = _
      rw [hcancel, parkerStandard_preserves_sign]
    rwa [hf] at hb
  · intro b
    have hf : α.val (loopSandwich e
        (parkerLoopMultiply (parkerSign (golayQuarterWeight e.1)
          (parkerSign s parkerOmega)) b)) =
        parkerLoopMultiply (parkerSign (golayHalfOverlap e.1 b.1) (α.val b))
          (parkerSign s parkerOmega) := by
      rw [parkerLoopMultiply_sign_left, loopSandwich_sign]
      change α.val (parkerSign (golayHalfOverlap e.1 (golayOne + b.1) +
        golayQuarterWeight e.1) (parkerSign (golayQuarterWeight e.1)
          (parkerLoopMultiply (parkerSign s parkerOmega) b))) = _
      rw [overlap_add_one, hcancel, parkerStandard_preserves_sign,
        α.prop.1, standard_signedOmega α hα, signedOmega_commutes,
        parkerLoopMultiply_sign_left]
    rcases h b with hb | hb
    · right
      have hh := congrArg (fun x => parkerLoopMultiply x (parkerSign s parkerOmega))
        (hf.symm.trans hb)
      rwa [signedOmega_twice] at hh
    · left
      exact (loopRight (parkerSign s parkerOmega)).injective (hf.symm.trans hb)

private theorem axis2_residual_sign (s : ParkerBit) (e : ParkerLoop)
    (α : ParkerStandardGroup)
    (h : ∀ b : ParkerLoop,
      parkerSign (golayHalfOverlap e.1 b.1) (α.val b) = b ∨
      parkerSign (golayHalfOverlap e.1 b.1) (α.val b) =
        parkerLoopMultiply b (parkerSign s parkerOmega)) :
    ∀ b : ParkerLoop, α.val b = parkerSign (golayHalfOverlap e.1 b.1) b := by
  have hp : parkerStandardProjection α = 1 := by
    apply parkerCodeEquiv_faithful_mod_golayOne
    intro a
    rcases h (a,0) with hb | hb
    · refine ⟨0, ?_⟩
      have hc := congrArg Prod.fst hb
      simpa only [parkerSign, parkerStandardProjection_spec, zero_smul, add_zero,
        parkerCodeEquiv_one] using hc
    · refine ⟨1, ?_⟩
      have hc : (α.val (a,0)).1 = a + golayOne := congrArg Prod.fst hb
      simpa only [parkerStandardProjection_spec, one_smul, parkerCodeEquiv_one] using hc
  intro b
  have hb : parkerSign (golayHalfOverlap e.1 b.1) (α.val b) = b := by
    rcases h b with hb | hb
    · exact hb
    · have hc : (α.val b).1 = b.1 + golayOne := congrArg Prod.fst hb
      rw [parkerStandardProjection_spec, hp, parkerCodeEquiv_one] at hc
      have hz : golayOne = 0 := add_left_cancel (hc.symm.trans (add_zero _).symm)
      exact (golayOne_ne_zero hz).elim
  exact (sign_twice _ _).symm.trans (congrArg (parkerSign (golayHalfOverlap e.1 b.1)) hb)

private theorem axis2_overlap_radical (e : ParkerLoop) (α : ParkerStandardGroup)
    (h : ∀ b : ParkerLoop, α.val b = parkerSign (golayHalfOverlap e.1 b.1) b) :
    e.1 = 0 ∨ e.1 = golayOne := by
  have hs : IsSignAutomorphism α.val := ⟨α.prop, fun b => by rw [h]; rfl⟩
  obtain ⟨c, hc⟩ := (isSignAutomorphism_iff_cocode α.val).mp hs
  have hf (b : golay) : cocodeDualEquiv c b = golayHalfOverlap e.1 b := by
    have he := congrArg Prod.snd (h (b,0))
    rw [← hc, parkerCocodeStandard_apply] at he
    simpa only [parkerSign, zero_add, cocodePairing] using he
  apply (parkerTripleIntersection_radical e.1).mp
  intro b c'
  have hadd : golayHalfOverlap e.1 (b + c') =
      golayHalfOverlap e.1 b + golayHalfOverlap e.1 c' := by
    rw [← hf, map_add, hf, hf]
  have ht := golayHalfOverlap_add_left b c' e.1
  rw [golayHalfOverlap_symmetric (b+c'), golayHalfOverlap_symmetric b,
    golayHalfOverlap_symmetric c', hadd] at ht
  have hz : parkerTripleIntersection b c' e.1 = 0 :=
    add_left_cancel (ht.symm.trans (add_zero _).symm)
  rwa [parkerTripleIntersection_cycle] at hz

/-- Fixing the signed-omega orbits on axis 2 forces exactly the central
normal-form coordinates. The sign parameter distinguishes the two kernels. -/
theorem axis2_normalForm_coordinates (s : ParkerBit) (d e : ParkerLoop)
    (α : ParkerStandardGroup) (hα : α.val parkerOmega = parkerOmega)
    (h : ∀ b : ParkerLoop,
      α.val (loopSandwich e (parkerLoopMultiply d b)) = b ∨
      α.val (loopSandwich e (parkerLoopMultiply d b)) =
        parkerLoopMultiply b (parkerSign s parkerOmega)) :
    (d = loopOne ∨ d = parkerSign s parkerOmega) ∧
      (e.1 = 0 ∨ e.1 = golayOne) ∧ α = 1 := by
  have hd := axis2_initial_coordinate s d e α hα h
  have hs := axis2_residual_sign s e α (axis2_remove_translation s d e α hα h)
  have he := axis2_overlap_radical e α hs
  have hq : golayQuarterWeight e.1 = 0 := by
    rcases he with he | he
    · rw [he, golayQuarterWeight_zero]
    · rw [he, quarterWeight_one]
  rw [hq, parkerSign_zero, parkerSign_zero] at hd
  refine ⟨hd, he, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro b
  change α.val b = b
  rw [hs]
  have hz : golayHalfOverlap e.1 b.1 = 0 := by
    rcases he with he | he
    · rw [he, golayHalfOverlap_zero_left]
    · rw [he, golayHalfOverlap_one]
  rw [hz, parkerSign_zero]

end Sporadic.Monster.Construction.TrialitySpin
