module
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.ProjectiveTorus

/-!
# The three-coordinate permutation action on frame tori

Reindexing the determinant-one triple `(a,b,(ab)⁻¹)` gives a genuine action
on the two norm-one coordinates. The predicates below state the literal
conjugation formula on the actual special and projective matrices. A special
action descends through the projective map, and either formula implies
normalization of the corresponding full torus.

These definitions separate the geometric construction of the normalizer
from its fixed-point and commutator calculations. No existence of such an
action for every normalizer element is asserted here.

Source: GLS4, Chapter 4, Lemma 3.11(c), and Chapter 2, Lemma 17.4.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.EvenInner
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

@[expose] def frameTriple (J : HermitianForm 3 E) (x : normOne J × normOne J) :
    Fin 3 → normOne J := ![x.1, x.2, (x.1 * x.2)⁻¹]

theorem frameTriple_prod (J : HermitianForm 3 E) (x : normOne J × normOne J) :
    ∏ i, frameTriple J x i = 1 := by
  simp [frameTriple, Fin.prod_univ_three, mul_assoc]

theorem frameTriple_injective (J : HermitianForm 3 E) :
    Function.Injective (frameTriple J) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

@[expose] def permuteFramePair (J : HermitianForm 3 E) (σ : Equiv.Perm (Fin 3))
    (x : normOne J × normOne J) : normOne J × normOne J :=
  (frameTriple J x (σ⁻¹ 0), frameTriple J x (σ⁻¹ 1))

theorem frameTriple_permute (J : HermitianForm 3 E) (σ : Equiv.Perm (Fin 3))
    (x : normOne J × normOne J) (i : Fin 3) :
    frameTriple J (permuteFramePair J σ x) i = frameTriple J x (σ⁻¹ i) := by
  have hp : ∏ i, frameTriple J x (σ⁻¹ i) = 1 :=
    (Equiv.prod_comp σ.symm (frameTriple J x)).trans (frameTriple_prod J x)
  rw [Fin.prod_univ_three] at hp
  fin_cases i
  · rfl
  · rfl
  · exact (eq_inv_of_mul_eq_one_right hp).symm

theorem permuteFramePair_mul (J : HermitianForm 3 E)
    (σ τ : Equiv.Perm (Fin 3)) (x : normOne J × normOne J) :
    permuteFramePair J (σ * τ) x = permuteFramePair J σ (permuteFramePair J τ x) := by
  apply frameTriple_injective J
  funext i
  simp only [frameTriple_permute, _root_.mul_inv_rev, Equiv.Perm.mul_apply]

theorem permuteFramePair_one (J : HermitianForm 3 E) (x : normOne J × normOne J) :
    permuteFramePair J 1 x = x := by rfl

theorem permuteFramePair_surjective (J : HermitianForm 3 E) (σ : Equiv.Perm (Fin 3)) :
    Function.Surjective (permuteFramePair J σ) := by
  intro x
  refine ⟨permuteFramePair J σ⁻¹ x, ?_⟩
  rw [← permuteFramePair_mul, mul_inv_cancel, permuteFramePair_one]

@[expose] def HasSpecialFrameAction (J : HermitianForm 3 E) (P : OrthogonalFrame J)
    (t : J.specialSubgroup) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ x, t * specialPairHom J P x * t⁻¹ = specialPairHom J P (permuteFramePair J σ x)

@[expose] def HasProjectiveFrameAction (J : HermitianForm 3 E) (P : OrthogonalFrame J)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ x, t * projectivePairHom J P x * t⁻¹ = projectivePairHom J P (permuteFramePair J σ x)

theorem HasSpecialFrameAction.projective (J : HermitianForm 3 E) (P : OrthogonalFrame J)
    (t : J.specialSubgroup) (σ : Equiv.Perm (Fin 3))
    (h : HasSpecialFrameAction J P t σ) :
    HasProjectiveFrameAction J P (J.specialToProjective t) σ := by
  intro x
  simpa only [projectivePairHom, MonoidHom.comp_apply, map_mul, map_inv] using congrArg J.specialToProjective (h x)

private theorem normalizes_range_of_action {A G : Type*} [Group A] [Group G]
    (f : A →* G) (t : G) (s : A → A) (hs : Function.Surjective s)
    (h : ∀ a, t * f a * t⁻¹ = f (s a)) : t ∈ normalizer f.range := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨s a, (h a).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := hs a
    refine ⟨b, ?_⟩
    apply (MulAut.conj t).injective
    exact (h b).trans ha

theorem HasSpecialFrameAction.mem_normalizer (J : HermitianForm 3 E)
    (P : OrthogonalFrame J) (t : J.specialSubgroup) (σ : Equiv.Perm (Fin 3))
    (h : HasSpecialFrameAction J P t σ) : t ∈ normalizer (specialFrameTorus J P) := by
  rw [← specialPairHom_range]
  exact normalizes_range_of_action (specialPairHom J P) t _
    (permuteFramePair_surjective J σ) h

theorem HasProjectiveFrameAction.mem_normalizer (J : HermitianForm 3 E)
    (P : OrthogonalFrame J) (t : ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : Equiv.Perm (Fin 3)) (h : HasProjectiveFrameAction J P t σ) :
    t ∈ normalizer (projectiveFrameTorus J P) := by
  rw [← projectivePairHom_range]
  exact normalizes_range_of_action (projectivePairHom J P) t _
    (permuteFramePair_surjective J σ) h

end UnitaryThree.OddTorusNormalizer
