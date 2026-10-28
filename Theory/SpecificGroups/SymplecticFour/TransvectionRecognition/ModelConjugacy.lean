module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.FieldExtraction.RankOneSchur
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# From an actual linear model to symplectic matrix conjugacy

For an irreducible symplectic action with a rank-one displacement, a linear
intertwiner pulls the target symplectic form back to a scalar multiple of the
original form. Rank-one Schur uniqueness proves this scalar assertion. In a
finite field of characteristic two, rescaling by a square root makes the
intertwiner symplectic without changing the intertwined action.

The coefficient-model theorem retains the actual subfield inclusion and
gives equality of matrix subgroups under conjugation by an actual matrix in
the ambient symplectic group.
Its moving-pair application keeps the transvection inside the generated pair;
it does not assert that the original central subgroup contains one.

This is the change-of-form step used in Aschbacher--Smith G.4.8--9 and the
conclusion of G.4.1, printed pp.340--342, applied to E.2.7, printed pp.219--220.
Construction of the native coefficient model and its intertwiner is an
independent representation-theoretic input.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open DiagramAutomorphisms.FieldFixedResidual
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Group G]

/-- A linear equivalence between the given actions can be rescaled to an
actual symplectic conjugating matrix. -/
theorem exists_symplectic_intertwiner_of_rank_one
    (ρ τ : G →* Sp F)
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp ρ))
    (d : G)
    (hr : Module.finrank F (LinearMap.range
      (((Representation.symplecticNatural 2).comp ρ) d - 1)) = 1)
    (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ x v, A (ρ x • v) = τ x • A v) :
    ∃ g : Sp F, ∀ x, g * ρ x * g⁻¹ = τ x := by
  let σ : Representation F G (Vector F) := (Representation.symplecticNatural 2).comp ρ
  letI : Representation.IsIrreducible σ := hi
  let B := (form F).comp A.toLinearMap A.toLinearMap
  have hB : ∀ x v w, B (σ x v) (σ x w) = B v w := by
    intro x v w
    change form F (A (ρ x • v)) (A (ρ x • w)) = form F (A v) (A w)
    rw [hA, hA, preserves_form]
  obtain ⟨c,hc⟩ := Representation.RankOneSchur.invariant_form_scalar_of_rank_one
    σ d hr (form F) TwoLocalCover.form_nondegenerate (fun x => preserves_form (ρ x)) B hB
  have hmul (v w : Vector F) : form F (A v) (A w) = c * form F v w := by
    exact congrArg (fun C : LinearMap.BilinForm F (Vector F) => C v w) hc
  have hc0 : c ≠ 0 := by
    intro hz
    have h := hmul (A.symm (e 0)) (A.symm (Pi.single (.inr 0) 1))
    simp [hz, form_apply, e, Pi.single_apply] at h
  obtain ⟨a,ha⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) c⁻¹
  change a ^ 2 = c⁻¹ at ha
  have hnorm : a * a * c = 1 := by rw [←pow_two,ha,inv_mul_cancel₀ hc0]
  let L : Module.End F (Vector F) := a • A.toLinearMap
  have hL (v w : Vector F) : form F (L v) (L w) = form F v w := by
    change form F (a • A v) (a • A w) = _
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hmul]
    calc
      a * (a * (c * form F v w)) = (a*a*c)*form F v w := by ring
      _ = form F v w := by rw [hnorm,one_mul]
  let g : Sp F := ⟨LinearMap.toMatrix' L, by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F)
      (LinearMap.toMatrix' L) (LinearMap.toMatrix' L)
    have hpres : (form F).comp L L = form F := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact hL v w
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg,Matrix.neg_mul,form] using hm⟩
  have hg (v : Vector F) : g • v = a • A v := LinearMap.toMatrix'_mulVec L v
  refine ⟨g,fun x => ?_⟩
  have hinter : g * ρ x = τ x * g := by
    apply Subtype.ext
    ext i j
    have h : (g * ρ x) • (Pi.single j (1 : F) : Vector F) =
        (τ x * g) • (Pi.single j (1 : F) : Vector F) := by
      simp only [mul_smul,hg,hA]
      exact ((toLinear (τ x)).map_smul a (A (Pi.single j (1 : F)))).symm
    exact congrFun (by simpa only [smul_eq_mulVec,Matrix.mulVec_single_one] using h) i
  rw [hinter,mul_assoc,mul_inv_cancel, mul_one]

/-- A literal coefficient model and its intertwiner yield the required
equality with a conjugate of the coefficient-inclusion range. -/
theorem exists_coefficient_conjugator_of_intertwiner
    (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (d : H)
    (hr : Module.finrank F (LinearMap.range
      (((Representation.symplecticNatural 2).comp H.subtype) d - 1)) = 1)
    (K : Subfield F) (eK : H ≃* Sp K) (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ x : H, ∀ v, A ((x : Sp F) • v) = coefficientInclusion K (eK x) • A v) :
    ∃ g : Sp F, H = (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := exists_symplectic_intertwiner_of_rank_one H.subtype
    ((coefficientInclusion K).comp eK.toMonoidHom) hi d hr A hA
  change ∀ x : H, g * (x : Sp F) * g⁻¹ = coefficientInclusion K (eK x) at hg
  refine ⟨g⁻¹,?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨coefficientInclusion K (eK ⟨x,hx⟩),⟨eK ⟨x,hx⟩,rfl⟩,?_⟩
    change g⁻¹ * coefficientInclusion K (eK ⟨x,hx⟩) * (g⁻¹)⁻¹ = x
    rw [←hg ⟨x,hx⟩]
    simp [mul_assoc]
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    obtain ⟨u,rfl⟩ := eK.surjective z
    have he : (MulAut.conj g⁻¹) (coefficientInclusion K (eK u)) = (u : Sp F) := by
      change g⁻¹ * coefficientInclusion K (eK u) * (g⁻¹)⁻¹ = u
      rw [←hg u]
      simp [mul_assoc]
    exact he.symm ▸ u.property

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition

namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open DiagramAutomorphisms EvenBorelTorus CentralRootGeometry
open DiagramAutomorphisms.FieldFixedResidual TransvectionRecognition
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The moving-pair hypotheses discharge irreducibility for the coefficient
conjugacy adapter. The native model and intertwiner remain explicit. -/
theorem exists_pair_coefficient_conjugator_of_moving_intertwiner
    (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom = V)
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hr : 2 < Nat.card V)
    (d : oppositePair V)
    (hd : Module.finrank F (LinearMap.range ((pairAction V) d - 1)) = 1)
    (K : Subfield F) (eK : oppositePair V ≃* Sp K)
    (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ x : oppositePair V, ∀ v,
      A ((x : Sp F) • v) = coefficientInclusion K (eK x) • A v) :
    ∃ g : Sp F, oppositePair V =
      (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom := by
  exact exists_coefficient_conjugator_of_intertwiner (oppositePair V)
    (pairAction_irreducible_of_moving_actor hq a ha V hV hc hr) d hd K eK A hA

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
