module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.FrobeniusReduction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius.Carrier

/-!
# Coefficient transport of the exceptional basic algebraic factors

For every field automorphism, simultaneous transport of a rational action and
its source F4 group gives a rational irreducible action with the same actual
highest weight. Positive-root fixation and simple-coroot eigenvalues are
verified on the transported vector. Under the explicit highest-weight
uniqueness premise, the transported factor is equivalent to the original one.
Semilinear conjugation of trace then identifies coefficient Frobenius with
precomposition by split Frobenius, including all its iterates.

Source: GLS3, Definition 2.8.3 and Remarks 2.8.4 and 2.8.8; Steinberg,
*Endomorphisms of Linear Algebraic Groups*, §13. Highest-weight uniqueness
remains an explicit premise for the classification assembly owner.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup.CoefficientTransport
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

@[simp] theorem carrierCoefficient_coroot (σ : F ≃+* F)
    (r : F4Chevalley.Root) (t : Fˣ) :
    (carrierCoefficientAction σ).equiv (algebraicCorootElement r t) =
      algebraicCorootElement r (Units.map (σ : F →+* F).toMonoidHom t) := by
  simp [algebraicCorootElement, algebraicNElement, map_mul, map_inv,
    carrierCoefficient_root]

/-- A semilinear intertwiner for the simultaneous coefficient action preserves
both the positive-root fixation and the actual simple-coroot eigenvalues. -/
theorem highestWeight_transport (σ : F ≃+* F)
    (B C : AlgebraicFactor F)
    (e : LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) B.Space C.Space)
    (he : ∀ g v, (C.action.action ((carrierCoefficientAction σ).equiv g) :
      Module.End F C.Space) (e v) = e ((B.action.action g : Module.End F B.Space) v))
    (weight : Fin 2 × Fin 2) (hv : HasBasicHighestWeight B weight) :
    HasBasicHighestWeight C weight := by
  obtain ⟨v, hv, hpos, htor⟩ := hv
  refine ⟨e v, by simpa using hv, ?_, ?_⟩
  · intro r hr t
    have h := he (algebraicRootElement r (σ.symm t)) v
    rw [carrierCoefficient_root, σ.apply_symm_apply, hpos r hr] at h
    exact h
  · intro i t
    let s : Fˣ := Units.map (σ.symm : F →+* F).toMonoidHom t
    have hs : Units.map (σ : F →+* F).toMonoidHom s = t := by
      apply Units.ext
      exact σ.apply_symm_apply t.val
    have h := he (algebraicCorootElement (typeF4SimpleRootIndex i) s) v
    rw [carrierCoefficient_coroot, hs, htor] at h
    rw [map_smulₛₗ, map_pow] at h
    change (C.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F C.Space) (e v) = (σ (σ.symm (t : F))) ^ _ • e v at h
    simpa only [σ.apply_symm_apply] using h

/-- Construct the rational irreducible coefficient transport of an algebraic
factor. No prime-field realization or character compatibility is assumed. -/
theorem exists_coefficientTransport (σ : F ≃+* F) (B : AlgebraicFactor F) :
    ∃ C : AlgebraicFactor F,
      ∃ e : LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) B.Space C.Space,
      ∀ g v, (C.action.action ((carrierCoefficientAction σ).equiv g) :
        Module.End F C.Space) (e v) = e ((B.action.action g : Module.End F B.Space) v) := by
  obtain ⟨b, f, hf⟩ := B.irreducible.1
  let e := basisCoefficientEquiv σ b
  let C : AlgebraicFactor F :=
    { Space := B.Space
      action := twistAction σ (carrierCoefficientAction σ).equiv B.action e
      irreducible := ⟨twistAction_rational σ (carrierCoefficientAction σ) B.action b f hf,
        twistAction_irreducible σ (carrierCoefficientAction σ).equiv B.action e B.irreducible.2⟩ }
  refine ⟨C, e, ?_⟩
  intro g v
  change ((twistAction σ (carrierCoefficientAction σ).equiv B.action e).action
    ((carrierCoefficientAction σ).equiv g) : Module.End F B.Space) (e v) = _
  rw [twistAction_apply, MulEquiv.symm_apply_apply]

/-- Trace comparison for the genuine transported factor, using only the
explicit highest-weight uniqueness premise. -/
theorem trace_coefficient (σ : F ≃+* F)
    (hunique : ∀ B C : AlgebraicFactor F, ∀ weight : Fin 2 × Fin 2,
      HasBasicHighestWeight B weight → HasBasicHighestWeight C weight →
        AreEquivalentRepresentations B.action C.action)
    (B : AlgebraicFactor F) (hB : B.IsExceptionalBasic)
    (g : Variety.Point (F4Chevalley.Carrier (k := F))) :
    σ (LinearMap.trace F B.Space (B.action.action g : Module.End F B.Space)) =
      LinearMap.trace F B.Space
        (B.action.action ((carrierCoefficientAction σ).equiv g) : Module.End F B.Space) := by
  obtain ⟨C, e, he⟩ := exists_coefficientTransport σ B
  obtain ⟨weight, hw⟩ := (isExceptionalBasic_iff B).mp hB
  obtain ⟨l, hl⟩ := hunique C B weight (highestWeight_transport σ B C e he weight hw) hw
  have hconj : e.conj (B.action.action g : Module.End F B.Space) =
      (C.action.action ((carrierCoefficientAction σ).equiv g) : Module.End F C.Space) := by
    ext w
    rw [LinearEquiv.conj_apply_apply, ← he, LinearEquiv.apply_symm_apply]
  have hlin : l.conj
      (C.action.action ((carrierCoefficientAction σ).equiv g) : Module.End F C.Space) =
      (B.action.action ((carrierCoefficientAction σ).equiv g) : Module.End F B.Space) := by
    ext w
    rw [LinearEquiv.conj_apply_apply]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      hl ((carrierCoefficientAction σ).equiv g) (l.symm w)
  rw [← LinearMap.trace_conj_semilinear σ _ e, hconj,
    ← LinearMap.trace_conj' _ l, hlin]

@[simp] theorem carrierCoefficient_embedding {k : ℕ}
    (σ : F ≃+* F) (f : CoefficientField k →+* F) (x : SplitGroup k) :
    (carrierCoefficientAction σ).equiv (splitEmbedding f x) =
      splitEmbedding ((σ : F →+* F).comp f) x := by
  have h : (carrierCoefficientAction σ).equiv.toMonoidHom.comp (splitEmbedding f) =
      splitEmbedding ((σ : F →+* F).comp f) := by
    apply splitGroup_hom_ext
    intro r t
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      splitEmbedding_rootGenerator, carrierCoefficient_root, RingHom.comp_apply]
    rfl
  exact DFunLike.congr_fun h x

variable [CharP F 2]

@[simp] theorem carrierCoefficient_frobenius {k : ℕ}
    (f : CoefficientField k →+* F) (x : SplitGroup k) :
    (carrierCoefficientAction (frobeniusEquiv F 2)).equiv (splitEmbedding f x) =
      splitEmbedding f (splitFrobeniusEnd k x) := by
  have h : (carrierCoefficientAction (frobeniusEquiv F 2)).equiv.toMonoidHom.comp
      (splitEmbedding f) = (splitEmbedding f).comp (splitFrobeniusEnd k) := by
    apply splitGroup_hom_ext
    intro r t
    simp [splitEmbedding_rootGenerator, carrierCoefficient_root,
      splitFrobeniusEnd, splitFrobenius_rootGenerator, frobeniusEquiv_apply, frobenius_def]
  exact DFunLike.congr_fun h x

/-- One Frobenius step for a basic factor at an arbitrary split-group point. -/
theorem trace_splitFrobenius {k : ℕ}
    (hunique : ∀ B C : AlgebraicFactor F, ∀ weight : Fin 2 × Fin 2,
      HasBasicHighestWeight B weight → HasBasicHighestWeight C weight →
        AreEquivalentRepresentations B.action C.action)
    (f : CoefficientField k →+* F) (B : AlgebraicFactor F) (hB : B.IsExceptionalBasic)
    (x : SplitGroup k) :
    LinearMap.trace F B.Space (B.action.action (splitEmbedding f x) : Module.End F B.Space) ^ 2 =
      LinearMap.trace F B.Space
        (B.action.action (splitEmbedding f (splitFrobeniusEnd k x)) : Module.End F B.Space) := by
  simpa only [frobeniusEquiv_apply, frobenius_def, carrierCoefficient_frobenius] using
    trace_coefficient (frobeniusEquiv F 2) hunique B hB (splitEmbedding f x)

/-- Iteration of genuine coefficient transport. -/
theorem trace_splitFrobenius_pow {k : ℕ}
    (hunique : ∀ B C : AlgebraicFactor F, ∀ weight : Fin 2 × Fin 2,
      HasBasicHighestWeight B weight → HasBasicHighestWeight C weight →
        AreEquivalentRepresentations B.action C.action)
    (f : CoefficientField k →+* F) (B : AlgebraicFactor F) (hB : B.IsExceptionalBasic)
    (r : ℕ) (x : SplitGroup k) :
    LinearMap.trace F B.Space (B.action.action (splitEmbedding f x) : Module.End F B.Space) ^
        (2 ^ r) =
      LinearMap.trace F B.Space
        (B.action.action (splitEmbedding f ((splitFrobeniusEnd k ^ r) x)) : Module.End F B.Space) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, pow_mul, ih, trace_splitFrobenius hunique f B hB]
      rw [pow_succ']
      rfl

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
