module

public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.Coordinates
public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.IntrinsicCoordinates.Frames
public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.FiniteCriterion

/-!
# Marked binary normal forms from intrinsic anisotropic factors

Every `AnisotropicFactors K` admits the actual multiplicative coordinates of
`MarkedCoordinates`. The factor quotients supply two independent lifts apiece;
collecting their ordered words defines a homomorphism from the 64-word model.
The lifts and the marked center generate both factors and hence the whole
group. Surjectivity and the common order 64 make this homomorphism bijective.
The intersection of the factors is exactly the center, so each factor is
precisely the locus where the other quotient plane vanishes.

The existence theorem uses neither a center action nor balanced square fibers.
Its consumer `exists_markedCoordinates_sixCases` adds precisely the original
balanced nonidentity central square fibers and applies the published finite
criterion. The identification of the six models with UT₃(F₄) belongs to the
separate root-recognition assembly.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and
the proof of 46.14, printed pp.29–30,251,257–258.
-/

public section

open Subgroup
namespace Theory.GroupTheory.AnisotropicRecognition
open Intrinsic
variable {K : Type*} [Group K] [Finite K] (F : AnisotropicFactors K)

omit [Finite K] in
private theorem center_le_first : center K ≤ F.A := F.inf_eq ▸ inf_le_left
omit [Finite K] in
private theorem center_le_second : center K ≤ F.B := F.inf_eq ▸ inf_le_right

private theorem wordEval_first {M : Cross} (P : FactorPair F.A F.z)
    (Q : FactorPair F.B F.u) (x : Word M) :
    wordEval (centerEquiv F).toMonoidHom P.a P.b Q.a Q.b x ∈ F.A ↔ x.vector.2 = 0 := by
  have ha := P.pairWord_mem x.vector.1
  have hb := Q.pairWord_mem x.vector.2
  have hz : centralEval (centerEquiv F).toMonoidHom x.central ∈ center K :=
    ((centerEquiv F) (Multiplicative.ofAdd x.central)).property
  change (pairWord P.a P.b x.vector.1 * pairWord Q.a Q.b x.vector.2) *
    centralEval (centerEquiv F).toMonoidHom x.central ∈ F.A ↔ _
  rw [F.A.mul_mem_cancel_right (center_le_first F hz), F.A.mul_mem_cancel_left ha]
  constructor
  · intro h
    exact (Q.pairWord_mem_center_iff _).mp (F.inf_eq ▸ (show
      pairWord Q.a Q.b x.vector.2 ∈ F.A ⊓ F.B from ⟨h,hb⟩))
  · intro h
    simp [h, pairWord]

private theorem wordEval_second {M : Cross} (P : FactorPair F.A F.z)
    (Q : FactorPair F.B F.u) (x : Word M) :
    wordEval (centerEquiv F).toMonoidHom P.a P.b Q.a Q.b x ∈ F.B ↔ x.vector.1 = 0 := by
  have ha := P.pairWord_mem x.vector.1
  have hb := Q.pairWord_mem x.vector.2
  have hz : centralEval (centerEquiv F).toMonoidHom x.central ∈ center K :=
    ((centerEquiv F) (Multiplicative.ofAdd x.central)).property
  change (pairWord P.a P.b x.vector.1 * pairWord Q.a Q.b x.vector.2) *
    centralEval (centerEquiv F).toMonoidHom x.central ∈ F.B ↔ _
  rw [F.B.mul_mem_cancel_right (center_le_second F hz), F.B.mul_mem_cancel_right hb]
  constructor
  · intro h
    exact (P.pairWord_mem_center_iff _).mp (F.inf_eq ▸ (show
      pairWord P.a P.b x.vector.1 ∈ F.A ⊓ F.B from ⟨ha,h⟩))
  · intro h
    simp [h, pairWord]

private noncomputable def evaluation (P : FactorPair F.A F.z) (Q : FactorPair F.B F.u) :
    Word (crossMatrix F P.a P.b Q.a Q.b) →* K :=
  wordHom (centerEquiv F).toMonoidHom (factorCollectionRelations F P Q)

private theorem evaluation_central (P : FactorPair F.A F.z) (Q : FactorPair F.B F.u)
    (r : Central) :
    evaluation F P Q (centralWord _ r) = centralEval (centerEquiv F).toMonoidHom r := by
  simp [evaluation, wordHom, wordEval, vectorWord, pairWord, centralWord]

private theorem evaluation_surjective (P : FactorPair F.A F.z) (Q : FactorPair F.B F.u) :
    Function.Surjective (evaluation F P Q) := by
  let f := evaluation F P Q
  let M := crossMatrix F P.a P.b Q.a Q.b
  have hz : center K ≤ f.range := by
    intro x hx
    obtain ⟨s, hs⟩ := (centerEquiv F).surjective ⟨x,hx⟩
    refine ⟨centralWord M s.toAdd, ?_⟩
    exact (evaluation_central F P Q s.toAdd).trans (congrArg Subtype.val hs)
  have ha : P.a ∈ f.range := by
    refine ⟨lift M va, ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, va]
  have hb : P.b ∈ f.range := by
    refine ⟨lift M vb, ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, vb]
  have hc : Q.a ∈ f.range := by
    refine ⟨lift M ((0,0),(1,0)), ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift]
  have hd : Q.b ∈ f.range := by
    refine ⟨lift M ((0,0),(0,1)), ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift]
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← F.sup_eq]
  exact sup_le (P.generate f.range hz ha hb) (Q.generate f.range hz hc hd)

/-- The two intrinsic anisotropic factors admit the published marked binary
normal forms. No assumption on the square fibers or on a center action is used. -/
theorem nonempty_markedCoordinates : Nonempty (MarkedCoordinates F) := by
  obtain ⟨P⟩ := nonempty_factorPair F F.A (center_le_first F) F.A_card F.z F.A_square
  obtain ⟨Q⟩ := nonempty_factorPair F F.B (center_le_second F) F.B_card F.u F.B_square
  let M := crossMatrix F P.a P.b Q.a Q.b
  let f := evaluation F P Q
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr
      ⟨evaluation_surjective F P Q, (card_Word M).trans F.card.symm⟩
  let e : Word M ≃* K := MulEquiv.ofBijective f hbij
  refine ⟨⟨M, e.symm, ?_, ?_, ?_, ?_⟩⟩
  · apply e.injective
    rw [e.apply_symm_apply]
    exact ((evaluation_central F P Q cz).trans
      (congrArg Subtype.val (centerEquiv_z F))).symm
  · apply e.injective
    rw [e.apply_symm_apply]
    exact ((evaluation_central F P Q cu).trans
      (congrArg Subtype.val (centerEquiv_u F))).symm
  · intro x
    rw [← wordEval_first F P Q (e.symm x)]
    change x ∈ F.A ↔ e (e.symm x) ∈ F.A
    rw [e.apply_symm_apply]
  · intro x
    rw [← wordEval_second F P Q (e.symm x)]
    change x ∈ F.B ↔ e (e.symm x) ∈ F.B
    rw [e.apply_symm_apply]

/-- Balanced nonidentity square fibers specialize the intrinsic normal forms
to the six matrices of the finite criterion. -/
theorem exists_markedCoordinates_sixCases
    (h : ∀ c d : center K, c ≠ 1 → d ≠ 1 →
      Nat.card {x : K // x^2 = (c : K)} = Nat.card {x : K // x^2 = (d : K)}) :
    ∃ C : MarkedCoordinates F, SixCases C.matrix := by
  obtain ⟨C⟩ := nonempty_markedCoordinates F
  exact ⟨C, sixCases_of_balanced C.matrix (firstNondegenerate_of_coordinates F C)
    (balanced_of_coordinates F C h)⟩

end Theory.GroupTheory.AnisotropicRecognition
