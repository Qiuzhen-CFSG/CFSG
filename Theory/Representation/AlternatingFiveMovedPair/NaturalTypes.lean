module
public import Theory.Representation.AlternatingFiveMovedPair.NaturalCommutant
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Basic
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Mathlib.RepresentationTheory.Intertwining
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.TensorModel
public import Theory.Representation.OrthogonalFourPlusMatrix.TensorRecognition
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Automorphisms

/-!
# The two binary natural tensor types for A₅ × A₅

An independently marked pair of natural SL₂(4) modules has exactly two binary
tensor types, according to its relative Frobenius twist. Common Frobenius on
the tensor removes one field twist; inner matrix actions remove inner markings.
The tensor flip handles factor exchange. Abstract semilinear coverage and the
product automorphism theorem therefore show that every product automorphism
permutes these two types by actual binary intertwining equivalences.

The scalar-commutant calculation distinguishes the two types. A final consumer
applies the cubic-free determinant recognition theorem and retains a specified
original factor marking, yielding a unique type for that source branch.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5 and D.3.7, printed
pp.195–199; GLS2 Theorem 25.14, Step 5, for the cubic-free tensor recognition.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open Representation.SL2FourNatural
open Representation.BinaryOffender.NaturalTensor
namespace Representation.AlternatingFiveMovedPair.NaturalTypes
abbrev Tensor := TensorSpace F
def tensorMatrixCoordinates : Tensor ≃ₗ[ZMod 2] (Fin 2 → Fin 2 → F) :=
  (tensorCoordinates F).restrictScalars (ZMod 2)
def matrixFrobenius : (Fin 2 → Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → Fin 2 → F) where
  toFun v i j := fieldFrobenius (v i j)
  invFun v i j := fieldFrobenius (v i j)
  left_inv v := by funext i j; exact fieldFrobenius_involutive _
  right_inv v := by funext i j; exact fieldFrobenius_involutive _
  map_add' v w := by funext i j; exact map_add fieldFrobenius _ _
  map_smul' c v := by funext i j; exact ZMod.map_smul fieldFrobenius c (v i j)
/-- Frobenius on both factors descends to the tensor over the four-element field. -/
def tensorFrobenius : Tensor ≃ₗ[ZMod 2] Tensor := tensorMatrixCoordinates.trans (matrixFrobenius.trans tensorMatrixCoordinates.symm)
theorem tensorFrobenius_tmul (x y : V) :
    tensorFrobenius (x ⊗ₜ[F] y) = frobeniusLinear x ⊗ₜ[F] frobeniusLinear y := by
  apply tensorMatrixCoordinates.injective
  simp only [tensorFrobenius, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change matrixFrobenius (tensorMatrixCoordinates (x ⊗ₜ[F] y)) = tensorMatrixCoordinates (frobeniusLinear x ⊗ₜ[F] frobeniusLinear y)
  funext i j
  change fieldFrobenius (tensorCoordinates F (x ⊗ₜ[F] y) i j) =
    tensorCoordinates F (frobeniusLinear x ⊗ₜ[F] frobeniusLinear y) i j
  rw [tensorCoordinates_tmul, tensorCoordinates_tmul, map_mul]
  rfl

theorem tensorFrobenius_intertwines (g : SL × SL) (v : Tensor) :
    tensorFrobenius (binaryTensorAction F g v) =
      binaryTensorAction F (slFrobenius g.1, slFrobenius g.2) (tensorFrobenius v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change tensorFrobenius (action g.1 x ⊗ₜ[F] action g.2 y) = _
    rw [tensorFrobenius_tmul, tensorFrobenius_tmul, frobenius_action, frobenius_action]
    rfl
  | add u v hu hv => simp only [map_add, hu, hv]

def fieldAut (b : Bool) : MulAut SL := if b then slFrobenius else 1
def model (b : Bool) : Representation (ZMod 2) (SL × SL) Tensor :=
  (binaryTensorAction F).comp ((MulEquiv.refl SL).prodCongr (fieldAut b)).toMonoidHom

private theorem automorphism_cases (a : MulAut SL) :
    ∃ (g : SL) (b : Bool), a = MulAut.conj g * fieldAut b := by
  obtain ⟨g, σ, hσ⟩ := Theory.PSL2.sl2_semilinear_coverage a
  rcases SemilinearNormalizer.fieldAutomorphism_cases σ with h | h
  · refine ⟨g, false, ?_⟩
    rw [hσ, h]
    congr 1
  · refine ⟨g, true, ?_⟩
    rw [hσ, h]
    congr 1

private def innerTwist {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (g : G) (a : MulAut G) :
    Representation.Equiv (ρ.comp (MulAut.conj g * a).toMonoidHom)
      (ρ.comp a.toMonoidHom) where
  toLinearEquiv := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g⁻¹)
  isIntertwining' h := by
    change ρ g⁻¹ ∘ₗ ρ (g * a h * g⁻¹) = ρ (a h) ∘ₗ ρ g⁻¹
    change ρ g⁻¹ * ρ (g * a h * g⁻¹) = ρ (a h) * ρ g⁻¹
    rw [← ρ.map_mul, ← ρ.map_mul]
    apply congrArg ρ
    simp only [mul_assoc, inv_mul_cancel_left]

private theorem fieldTwist_types (a b : Bool) :
    ∃ c : Bool, Nonempty (Representation.Equiv ((binaryTensorAction F).comp
      ((fieldAut a).prodCongr (fieldAut b)).toMonoidHom) (model c)) := by
  cases a with
  | false =>
    refine ⟨b, ⟨?_⟩⟩
    exact Representation.Equiv.refl _
  | true =>
    refine ⟨!b, ⟨Representation.Equiv.mk tensorFrobenius ?_⟩⟩
    intro g
    apply LinearMap.ext
    intro v
    change tensorFrobenius (binaryTensorAction F (slFrobenius g.1, fieldAut b g.2) v) =
      binaryTensorAction F (g.1, fieldAut (!b) g.2) (tensorFrobenius v)
    rw [tensorFrobenius_intertwines, slFrobenius_involutive]
    cases b <;> simp only [fieldAut, Bool.false_eq_true, if_false, Bool.not_false,
      Bool.not_true, if_true, MulAut.one_apply, slFrobenius_involutive]

/-- Independent markings produce one of the two relative Frobenius types. -/
theorem independent_marking_types (a b : MulAut SL) :
    ∃ c : Bool, Nonempty (Representation.Equiv ((binaryTensorAction F).comp
      (a.prodCongr b).toMonoidHom) (model c)) := by
  obtain ⟨g, i, rfl⟩ := automorphism_cases a
  obtain ⟨h, j, rfl⟩ := automorphism_cases b
  obtain ⟨c, ⟨e⟩⟩ := fieldTwist_types i j
  have he : (MulAut.conj g * fieldAut i).prodCongr (MulAut.conj h * fieldAut j) =
      MulAut.conj (g,h) * (fieldAut i).prodCongr (fieldAut j) := by
    ext x <;> rfl
  rw [he]
  exact ⟨c, ⟨(innerTwist (binaryTensorAction F) (g,h)
    ((fieldAut i).prodCongr (fieldAut j))).trans e⟩⟩

private theorem product_automorphism_cases (φ : MulAut (SL × SL)) :
    (∃ a b : MulAut SL, φ = a.prodCongr b) ∨
    (∃ a b : MulAut SL, φ = a.prodCongr b * MulEquiv.prodComm) := by
  let e := alternatingFiveEquiv.prodCongr alternatingFiveEquiv
  let ψ := MulAut.congr e φ
  rcases BinaryPermutation.FiveTensorSquare.product_automorphism_alternatives ψ with
    ⟨a,b,h⟩ | ⟨a,b,h⟩
  · left
    refine ⟨MulAut.congr alternatingFiveEquiv.symm a,
      MulAut.congr alternatingFiveEquiv.symm b, ?_⟩
    apply MulEquiv.ext
    intro g
    apply e.injective
    have hh := h (e g)
    change e (φ (e.symm (e g))) = (a (e g).1, b (e g).2) at hh
    rw [e.symm_apply_apply] at hh
    change e (φ g) = (alternatingFiveEquiv (alternatingFiveEquiv.symm (a (e g).1)),
      alternatingFiveEquiv (alternatingFiveEquiv.symm (b (e g).2)))
    simpa only [MulEquiv.apply_symm_apply] using hh
  · right
    refine ⟨MulAut.congr alternatingFiveEquiv.symm a,
      MulAut.congr alternatingFiveEquiv.symm b, ?_⟩
    apply MulEquiv.ext
    intro g
    apply e.injective
    have hh := h (e g)
    change e (φ (e.symm (e g))) = (a (e g).2, b (e g).1) at hh
    rw [e.symm_apply_apply] at hh
    change e (φ g) = (alternatingFiveEquiv (alternatingFiveEquiv.symm (a (e g).2)),
      alternatingFiveEquiv (alternatingFiveEquiv.symm (b (e g).1)))
    simpa only [MulEquiv.apply_symm_apply] using hh

private def compEquiv {G H W U : Type*} [Monoid G] [Monoid H]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) G W} {σ : Representation (ZMod 2) G U}
    (e : Representation.Equiv ρ σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv (fun g => e.isIntertwining' (f g))

private def flipEquiv :
    Representation.Equiv (binaryTensorAction F)
      ((binaryTensorAction F).comp (MulEquiv.prodComm : MulAut (SL × SL)).toMonoidHom) := by
  refine Representation.Equiv.mk
    ((_root_.TensorProduct.comm F V V).restrictScalars (ZMod 2)) ?_
  intro g
  apply LinearMap.ext
  intro v
  exact tensorFlip_intertwines F g v

/-- Every abstract product automorphism carries the natural tensor to one
of the two literal descent types. -/
theorem product_automorphism_types (φ : MulAut (SL × SL)) :
    ∃ c : Bool, Nonempty (Representation.Equiv ((binaryTensorAction F).comp
      φ.toMonoidHom) (model c)) := by
  rcases product_automorphism_cases φ with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩
  · exact independent_marking_types a b
  · obtain ⟨c, ⟨e⟩⟩ := independent_marking_types b a
    refine ⟨c, ⟨?_⟩⟩
    have f := compEquiv flipEquiv
      (a.prodCongr b * (MulEquiv.prodComm : MulAut (SL × SL))).toMonoidHom
    exact f.trans e

/-- The chosen baseline marking is retained; independent source markings
leave exactly the two relative tensor types. -/
theorem marked_types {J : Type*} [Group J] (base a b : J ≃* SL) :
    ∃ c : Bool, Nonempty (Representation.Equiv
      ((binaryTensorAction F).comp (a.prodCongr b).toMonoidHom)
      ((model c).comp (base.prodCongr base).toMonoidHom)) := by
  obtain ⟨c, ⟨e⟩⟩ := independent_marking_types (base.symm.trans a) (base.symm.trans b)
  refine ⟨c, ⟨?_⟩⟩
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  have hh := e.isIntertwining' (base g.1, base g.2)
  change e.toLinearMap ∘ₗ binaryTensorAction F (a (base.symm (base g.1)),
    b (base.symm (base g.2))) = model c (base g.1, base g.2) ∘ₗ e.toLinearMap at hh
  change e.toLinearMap ∘ₗ binaryTensorAction F (a g.1, b g.2) =
    model c (base g.1, base g.2) ∘ₗ e.toLinearMap
  simpa only [MulEquiv.symm_apply_apply] using hh

/-- Both descent types are closed under all product automorphisms. -/
theorem model_automorphism_types (φ : MulAut (SL × SL)) (b : Bool) :
    ∃ c : Bool, Nonempty (Representation.Equiv ((model b).comp φ.toMonoidHom) (model c)) := by
  exact product_automorphism_types (((MulEquiv.refl SL).prodCongr (fieldAut b)) * φ)

/-- The two Boolean labels are the literal models used by the displacement bounds. -/
@[simp] theorem model_false : model false = Natural.first := rfl
@[simp] theorem model_true : model true = Natural.second := rfl

/-- Alternating tensor coordinates retain both acting factors literally. -/
def determinantEquiv : Representation.Equiv (binaryTensorAction F)
    ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
  refine Representation.Equiv.mk
    ((RankTwo.OrthogonalFour.tensorCoordinates (K := F)).restrictScalars (ZMod 2)) ?_
  intro g
  apply LinearMap.ext
  intro v
  exact RankTwo.OrthogonalFour.tensorCoordinates_equivariant g v

/-- A determinant-model identification with arbitrary factor markings reduces
against a fixed baseline to the same two concrete tensor types. -/
theorem determinant_marked_types {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (J × J) W) (base a b : J ≃* SL)
    (h : Nonempty (Representation.Equiv ρ
      (ClassicalOrthogonal.FourPlusMatrix.Binary.action.comp (a.prodCongr b).toMonoidHom))) :
    ∃ c : Bool, Nonempty (Representation.Equiv ρ
      ((model c).comp (base.prodCongr base).toMonoidHom)) := by
  obtain ⟨e⟩ := h
  obtain ⟨c, ⟨f⟩⟩ := marked_types base a b
  exact ⟨c, ⟨e.trans ((compEquiv determinantEquiv.symm (a.prodCongr b).toMonoidHom).trans f)⟩⟩

/-- The source cubic-free irreducible product branch has exactly the two
natural descent types, under its specified baseline marking. -/
theorem cubicFree_marked_types {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Group.IsPerfect (QuadraticFourGroup.Factor 2)]
    (ρ : Representation (ZMod 2)
      (QuadraticFourGroup.Factor 2 × QuadraticFourGroup.Factor 2) W)
    [ρ.IsIrreducible]
    (h : QuadraticFourGroup.TensorClassification.CubicFreeOnFactors ρ)
    (base : QuadraticFourGroup.Factor 2 ≃* SL) :
    ∃ c : Bool, Nonempty (Representation.Equiv ρ
      ((model c).comp (base.prodCongr base).toMonoidHom)) := by
  obtain ⟨a,b,he⟩ := ClassicalOrthogonal.FourPlusMatrix.TensorRecognition.exists_binary_determinant_equiv ρ h
  exact determinant_marked_types ρ base a b he

private def uncompEquiv {G W U : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) G W} {σ : Representation (ZMod 2) G U}
    (a : MulAut G)
    (e : Representation.Equiv (ρ.comp a.toMonoidHom) (σ.comp a.toMonoidHom)) :
    Representation.Equiv ρ σ := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  have h := e.isIntertwining' (a.symm g)
  change e.toLinearMap ∘ₗ ρ (a (a.symm g)) = σ (a (a.symm g)) ∘ₗ e.toLinearMap at h
  simpa only [MulEquiv.apply_symm_apply] using h

private theorem model_label_unique_aux
    (hne : ¬ Nonempty (Representation.Equiv Natural.first Natural.second))
    {b c : Bool} (h : Nonempty (Representation.Equiv (model b) (model c))) : b = c := by
  cases b <;> cases c
  · rfl
  · exact False.elim (hne h)
  · exact False.elim (hne ⟨(Classical.choice h).symm⟩)
  · rfl

private theorem model_automorphism_permutation_aux
    (hne : ¬ Nonempty (Representation.Equiv Natural.first Natural.second))
    (φ : MulAut (SL × SL)) :
    ∃ p : Equiv.Perm Bool, ∀ b : Bool,
      Nonempty (Representation.Equiv ((model b).comp φ.toMonoidHom) (model (p b))) := by
  choose f hf using model_automorphism_types φ
  have hi : Function.Injective f := by
    intro a b hab
    obtain ⟨ea⟩ := hf a
    obtain ⟨eb⟩ := hf b
    rw [hab] at ea
    exact model_label_unique_aux hne ⟨uncompEquiv φ (ea.trans eb.symm)⟩
  exact ⟨Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩, hf⟩

/-- The relative Frobenius label is determined by the binary module type. -/
theorem model_label_unique {b c : Bool}
    (h : Nonempty (Representation.Equiv (model b) (model c))) : b = c :=
  model_label_unique_aux NaturalCommutant.first_second_not_equiv h

/-- Precisely equal labels represent equivalent binary product modules. -/
theorem model_equiv_iff (b c : Bool) :
    Nonempty (Representation.Equiv (model b) (model c)) ↔ b = c := by
  constructor
  · exact model_label_unique
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

/-- Every product automorphism permutes the two literal natural tensor types,
with an actual binary intertwining equivalence for each constituent. -/
theorem model_automorphism_permutation (φ : MulAut (SL × SL)) :
    ∃ p : Equiv.Perm Bool, ∀ b : Bool,
      Nonempty (Representation.Equiv ((model b).comp φ.toMonoidHom) (model (p b))) :=
  model_automorphism_permutation_aux NaturalCommutant.first_second_not_equiv φ

private def uncompSurjective {G H W U : Type*} [Monoid G] [Monoid H]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) G W} {σ : Representation (ZMod 2) G U}
    (f : H →* G) (hf : Function.Surjective f)
    (e : Representation.Equiv (ρ.comp f) (σ.comp f)) : Representation.Equiv ρ σ := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  obtain ⟨h, rfl⟩ := hf g
  exact e.isIntertwining' h

/-- A fixed original marking makes the two-type classification unique. -/
theorem marked_label_unique {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (J × J) W) (base : J ≃* SL)
    {b c : Bool}
    (hb : Nonempty (Representation.Equiv ρ
      ((model b).comp (base.prodCongr base).toMonoidHom)))
    (hc : Nonempty (Representation.Equiv ρ
      ((model c).comp (base.prodCongr base).toMonoidHom))) : b = c := by
  obtain ⟨eb⟩ := hb
  obtain ⟨ec⟩ := hc
  exact model_label_unique ⟨uncompSurjective (base.prodCongr base).toMonoidHom
    (base.prodCongr base).surjective (eb.symm.trans ec)⟩

/-- The actual cubic-free source branch has a unique descent label relative
to its original, specified factor marking. -/
theorem cubicFree_marked_unique_type {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Group.IsPerfect (QuadraticFourGroup.Factor 2)]
    (ρ : Representation (ZMod 2)
      (QuadraticFourGroup.Factor 2 × QuadraticFourGroup.Factor 2) W)
    [ρ.IsIrreducible]
    (h : QuadraticFourGroup.TensorClassification.CubicFreeOnFactors ρ)
    (base : QuadraticFourGroup.Factor 2 ≃* SL) :
    ∃! c : Bool, Nonempty (Representation.Equiv ρ
      ((model c).comp (base.prodCongr base).toMonoidHom)) := by
  obtain ⟨c, hc⟩ := cubicFree_marked_types ρ h base
  exact ⟨c, hc, fun d hd => marked_label_unique ρ base hd hc⟩

private def prodEquiv {G U V W X : Type*} [Monoid G]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {a : Representation (ZMod 2) G U} {b : Representation (ZMod 2) G V}
    {c : Representation (ZMod 2) G W} {d : Representation (ZMod 2) G X}
    (e : Representation.Equiv a c) (f : Representation.Equiv b d) :
    Representation.Equiv (a.prod b) (c.prod d) := by
  refine Representation.Equiv.mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) ?_
  intro g
  apply LinearMap.ext
  intro v
  exact Prod.ext (LinearMap.congr_fun (e.isIntertwining' g) v.1)
    (LinearMap.congr_fun (f.isIntertwining' g) v.2)

private def prodSwap {G U V : Type*} [Monoid G]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]
    (a : Representation (ZMod 2) G U) (b : Representation (ZMod 2) G V) :
    Representation.Equiv (a.prod b) (b.prod a) := by
  refine Representation.Equiv.mk (LinearEquiv.prodComm (ZMod 2) U V) ?_
  intro g
  rfl

/-- The entire natural moved pair admits every automorphism of the original
product, with an actual binary equivalence retaining the specified group map. -/
theorem naturalPair_automorphism_equiv (φ : MulAut (SL × SL)) :
    Nonempty (Representation.Equiv (Natural.action.comp φ.toMonoidHom) Natural.action) := by
  obtain ⟨p, hp⟩ := model_automorphism_permutation φ
  obtain ⟨e₀⟩ := hp false
  obtain ⟨e₁⟩ := hp true
  have hdiff : p true ≠ p false := fun h => Bool.noConfusion (p.injective h)
  cases hpf : p false with
  | false =>
    have hpt : p true = true := by
      cases ht : p true
      · exact False.elim (hdiff (ht.trans hpf.symm))
      · rfl
    rw [hpf] at e₀
    rw [hpt] at e₁
    exact ⟨prodEquiv e₀ e₁⟩
  | true =>
    have hpt : p true = false := by
      cases ht : p true
      · rfl
      · exact False.elim (hdiff (ht.trans hpf.symm))
    rw [hpf] at e₀
    rw [hpt] at e₁
    exact ⟨(prodEquiv e₀ e₁).trans (prodSwap Natural.second Natural.first)⟩

end Representation.AlternatingFiveMovedPair.NaturalTypes
