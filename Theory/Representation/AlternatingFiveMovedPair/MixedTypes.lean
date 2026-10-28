module
public import Theory.Representation.AlternatingFiveMovedPair.Mixed
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Exchange
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Automorphisms
/-!
# The two mixed binary A₅ product-module types

The natural and deleted four-dimensional binary A₅ modules both extend to
S₅. Their extensions implement every factor automorphism, so factor-preserving
automorphisms fix N⊗D and D⊗N, while factor exchange interchanges the types.
Cubic freeness distinguishes the literal factor labels. Explicit field
coordinates absorb an arbitrary natural marking and identify both types with
the exact summands used by the moved-pair displacement model, retaining a
single chosen baseline for both factors.

Source: Aschbacher–Smith D.3.5, printed pp.195–196. This is type transport
only; the displacement and full-normalizer estimates belong to the model.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open Representation.QuadraticFourGroup.TensorClassification
namespace Representation.AlternatingFiveMovedPair.MixedTypes
open SL2FourNatural SL2FourNatural.SemilinearNormalizer
abbrev Alt := alternatingGroup (Fin 5)
abbrev Sym := Equiv.Perm (Fin 5)
abbrev natural : Representation (ZMod 2) Alt Mixed.Natural :=
  Mixed.naturalAction.comp Alt.subtype
abbrev deleted : Representation (ZMod 2) Alt Mixed.Deleted :=
  Mixed.deletedAction.comp Alt.subtype
abbrev first : Representation (ZMod 2) (Alt × Alt) Mixed.ND :=
  externalTensor natural deleted
abbrev second : Representation (ZMod 2) (Alt × Alt) Mixed.DN :=
  externalTensor deleted natural

def baseline : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  alternatingFiveEquiv.symm.trans standardGroupEquiv

private theorem extension_twist {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) Sym U) (a : MulAut Alt) :
    Nonempty (Representation.Equiv (ρ.comp Alt.subtype) ((ρ.comp Alt.subtype).comp a.toMonoidHom)) := by
  obtain ⟨s, hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective a
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective (ρ s) (ρ.apply_bijective s)) ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  change ρ s (ρ g.val v) = ρ (a g).val (ρ s v)
  rw [←hs]
  change ρ s (ρ g.val v) = ρ (s*g.val*s⁻¹) (ρ s v)
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

theorem natural_twist (a : MulAut Alt) :
    Nonempty (natural.Equiv (natural.comp a.toMonoidHom)) :=
  extension_twist Mixed.naturalAction a

theorem deleted_twist (a : MulAut Alt) :
    Nonempty (deleted.Equiv (deleted.comp a.toMonoidHom)) :=
  extension_twist Mixed.deletedAction a

def core_deleted : BinaryPermutation.FiveTensorSquare.δ.Equiv deleted :=
  Representation.Equiv.mk (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)) (by
    intro g
    apply LinearMap.ext
    intro v
    exact BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)


local instance canonicalBinaryAlgebra : Algebra (ZMod 2) (GaloisField 2 2) := ZMod.algebra _ 2

/-- The canonical-field coordinates with the scalar convention of BinarySmall. -/
private def standardCoordinates : V ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) where
  toFun v i := fieldEquiv (v i)
  invFun v i := fieldEquiv.symm (v i)
  left_inv v := by funext i; exact fieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact fieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add fieldEquiv _ _
  map_smul' c v := by
    funext i
    exact ZMod.map_smul fieldEquiv c (v i)

theorem natural_marking (f : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
    Nonempty (Representation.Equiv (SL2.BinarySmall.natural.comp f.toMonoidHom) natural) := by
  let a : MulAut Alt := (f.trans standardGroupEquiv.symm).trans alternatingFiveEquiv
  let A (g : Alt) := standardGroupEquiv.symm (f g)
  have ha (g : Alt) : (a g : Sym) = specialFiveLines (A g) := rfl
  let e : Representation.Equiv (SL2.BinarySmall.natural.comp f.toMonoidHom)
      (natural.comp a.toMonoidHom) :=
    Representation.Equiv.mk standardCoordinates.symm (by
      intro g
      apply LinearMap.ext
      intro v
      change standardCoordinates.symm (SL2.BinarySmall.natural (f g) v) =
        Mixed.naturalAction (a g).val (standardCoordinates.symm v)
      rw [ha, Mixed.naturalAction_special]
      apply standardCoordinates.injective
      rw [standardCoordinates.apply_symm_apply]
      change _ = standardVectorEquiv (action (A g) (standardCoordinates.symm v))
      rw [standard_equivariant]
      have he (v : V) : standardVectorEquiv v = standardCoordinates v := rfl
      rw [he, standardCoordinates.apply_symm_apply]
      simp only [A, MulEquiv.apply_symm_apply]
      rfl)
  obtain ⟨ea⟩ := natural_twist a
  exact ⟨e.trans ea.symm⟩

private def compEquiv {G H W U : Type*} [Monoid G] [Monoid H]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) G W} {σ : Representation (ZMod 2) G U}
    (e : Representation.Equiv ρ σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv (fun g => e.isIntertwining' (f g))

theorem first_factorwise (a b : MulAut Alt) :
    Nonempty (Representation.Equiv (first.comp (a.prodCongr b).toMonoidHom) first) := by
  obtain ⟨ea⟩ := natural_twist a
  obtain ⟨eb⟩ := deleted_twist b
  exact ⟨(externalTensorEquiv ea eb).symm⟩

theorem second_factorwise (a b : MulAut Alt) :
    Nonempty (Representation.Equiv (second.comp (a.prodCongr b).toMonoidHom) second) := by
  obtain ⟨ea⟩ := deleted_twist a
  obtain ⟨eb⟩ := natural_twist b
  exact ⟨(externalTensorEquiv ea eb).symm⟩

def first_swap : Representation.Equiv
    (first.comp (MulEquiv.prodComm : MulAut (Alt × Alt)).toMonoidHom) second :=
  Representation.Equiv.mk (_root_.TensorProduct.comm (ZMod 2) _ _) (by
    intro g
    ext u v
    rfl)

def second_swap : Representation.Equiv
    (second.comp (MulEquiv.prodComm : MulAut (Alt × Alt)).toMonoidHom) first :=
  Representation.Equiv.mk (_root_.TensorProduct.comm (ZMod 2) _ _) (by
    intro g
    ext u v
    rfl)

theorem first_factor_exchanging (a b : MulAut Alt) :
    Nonempty (Representation.Equiv
      (first.comp (a.prodCongr b * (MulEquiv.prodComm : MulAut (Alt × Alt))).toMonoidHom)
      second) := by
  obtain ⟨e⟩ := first_factorwise a b
  exact ⟨(compEquiv e (MulEquiv.prodComm : MulAut (Alt × Alt)).toMonoidHom).trans first_swap⟩

theorem second_factor_exchanging (a b : MulAut Alt) :
    Nonempty (Representation.Equiv
      (second.comp (a.prodCongr b * (MulEquiv.prodComm : MulAut (Alt × Alt))).toMonoidHom)
      first) := by
  obtain ⟨e⟩ := second_factorwise a b
  exact ⟨(compEquiv e (MulEquiv.prodComm : MulAut (Alt × Alt)).toMonoidHom).trans second_swap⟩

/-- All product automorphisms preserve both types or exchange both types. -/
theorem product_automorphism_types (a : MulAut (Alt × Alt)) :
    (Nonempty (Representation.Equiv (first.comp a.toMonoidHom) first) ∧
      Nonempty (Representation.Equiv (second.comp a.toMonoidHom) second)) ∨
    (Nonempty (Representation.Equiv (first.comp a.toMonoidHom) second) ∧
      Nonempty (Representation.Equiv (second.comp a.toMonoidHom) first)) := by
  rcases BinaryPermutation.FiveTensorSquare.product_automorphism_alternatives a with
    ⟨b,c,h⟩ | ⟨b,c,h⟩
  · have ha : a = b.prodCongr c := MulEquiv.ext h
    rw [ha]
    exact Or.inl ⟨first_factorwise b c, second_factorwise b c⟩
  · have ha : a = b.prodCongr c * (MulEquiv.prodComm : MulAut (Alt × Alt)) := MulEquiv.ext h
    rw [ha]
    exact Or.inr ⟨first_factor_exchanging b c, second_factor_exchanging b c⟩

/-- The deleted/natural source alternative has the fixed second marking. -/
theorem deleted_natural_marking
    (f : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
    Nonempty (Representation.Equiv
      (externalTensor BinaryPermutation.FiveTensorSquare.δ
        (SL2.BinarySmall.natural.comp f.toMonoidHom)) second) := by
  obtain ⟨e⟩ := natural_marking f
  exact ⟨externalTensorEquiv core_deleted e⟩

/-- The natural/deleted source alternative has the fixed first marking. -/
theorem natural_deleted_marking
    (f : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
    Nonempty (Representation.Equiv
      (externalTensor (SL2.BinarySmall.natural.comp f.toMonoidHom)
        BinaryPermutation.FiveTensorSquare.δ) first) := by
  obtain ⟨e⟩ := natural_marking f
  exact ⟨externalTensorEquiv e core_deleted⟩


/-- Cubic freeness detects the natural factor under the fixed marking. -/
theorem natural_cubic_free : CubicFixedPointFree natural := by
  obtain ⟨e⟩ := natural_marking baseline
  apply CubicFixedPointFree.of_equiv (e := e)
  intro g hg v hv
  exact Matrix.SL2.cubic_fixed_eq_zero (baseline g)
    ((orderOf_injective baseline.toMonoidHom baseline.injective g).trans hg) v hv

private theorem right_fixed_of_factor (g : Alt) (hg : FixedPointFreeAt natural g) :
    FixedPointFreeAt second (1,g) := by
  intro x hx
  let b := Module.finBasis (ZMod 2) Mixed.Deleted
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := Mixed.Natural) b
  have he (x : Mixed.DN) (i) :
      e (second (1,g) x) i = natural g (e x i) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      change e (deleted 1 u ⊗ₜ[ZMod 2] natural g v) i = _
      simp [e]
    | add x y hx hy => simpa only [map_add,Finsupp.add_apply] using congrArg₂ (· + ·) hx hy
  apply e.injective
  apply Finsupp.ext
  intro i
  simpa only [map_zero,Finsupp.zero_apply] using hg (e x i) (by rw [←he,hx])

private theorem left_fixed_of_factor (g : Alt) (hg : FixedPointFreeAt natural g) :
    FixedPointFreeAt first (g,1) := by
  exact (right_fixed_of_factor g hg).of_equiv
    (show Representation.Equiv second
      (first.comp (MulEquiv.prodComm : MulAut (Alt × Alt)).toMonoidHom) from first_swap.symm)

theorem first_left_cubic_free : ∀ g, orderOf g = 3 → FixedPointFreeAt first (g,1) :=
  fun g hg => left_fixed_of_factor g (natural_cubic_free g hg)

theorem second_right_cubic_free : ∀ g, orderOf g = 3 → FixedPointFreeAt second (1,g) :=
  fun g hg => right_fixed_of_factor g (natural_cubic_free g hg)

private theorem deleted_not_cubic_free : ¬ CubicFixedPointFree deleted := by
  intro hf
  obtain ⟨g,hg,v,hv,hfix⟩ := BinaryPermutation.AlternatingFiveLinearTwo.exists_cubic_fixed_ne_zero
  exact hv (((hf g hg).of_equiv core_deleted.symm) v hfix)

/-- The first orientation is not cubic-free on its deleted right factor. -/
theorem first_not_right_cubic_free :
    ¬ (∀ g, orderOf g = 3 → FixedPointFreeAt first (1,g)) := by
  intro hf
  apply deleted_not_cubic_free
  intro g hg
  exact (hf g hg).right_of_externalTensor

/-- The second orientation is not cubic-free on its deleted left factor. -/
theorem second_not_left_cubic_free :
    ¬ (∀ g, orderOf g = 3 → FixedPointFreeAt second (g,1)) := by
  intro hf
  apply deleted_not_cubic_free
  intro g hg
  exact (hf g hg).left_of_externalTensor

/-- The two mixed types are distinct under their literal factor labels. -/
theorem first_second_not_equiv : ¬ Nonempty (Representation.Equiv first second) := by
  rintro ⟨e⟩
  apply second_not_left_cubic_free
  intro g hg
  exact (first_left_cubic_free g hg).of_equiv e


/-- The exact first summand of the displacement model, on its original SL factors. -/
abbrev firstSL : Representation (ZMod 2) (SL × SL) Mixed.ND :=
  Mixed.first.comp (specialFiveLines.prodMap specialFiveLines)

/-- The exact second summand of the displacement model, on its original SL factors. -/
abbrev secondSL : Representation (ZMod 2) (SL × SL) Mixed.DN :=
  Mixed.second.comp (specialFiveLines.prodMap specialFiveLines)

/-- A single baseline for both factors identifies the first source type
with the first displacement-model summand. -/
theorem first_marked_model (base : Alt ≃* SL) :
    Nonempty (Representation.Equiv first
      (firstSL.comp (base.prodCongr base).toMonoidHom)) := by
  let a : MulAut Alt := base.trans alternatingFiveEquiv
  obtain ⟨e⟩ := first_factorwise a a
  exact ⟨e.symm⟩

/-- The same baseline identifies the second source type with the second
summand; both markings are retained literally. -/
theorem second_marked_model (base : Alt ≃* SL) :
    Nonempty (Representation.Equiv second
      (secondSL.comp (base.prodCongr base).toMonoidHom)) := by
  let a : MulAut Alt := base.trans alternatingFiveEquiv
  obtain ⟨e⟩ := second_factorwise a a
  exact ⟨e.symm⟩

/-- Arbitrary source natural markings normalize against one shared model baseline. -/
theorem natural_deleted_marked_model
    (f : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (base : Alt ≃* SL) :
    Nonempty (Representation.Equiv
      (externalTensor (SL2.BinarySmall.natural.comp f.toMonoidHom)
        BinaryPermutation.FiveTensorSquare.δ)
      (firstSL.comp (base.prodCongr base).toMonoidHom)) := by
  obtain ⟨e⟩ := natural_deleted_marking f
  obtain ⟨b⟩ := first_marked_model base
  exact ⟨e.trans b⟩

/-- Arbitrary source natural markings normalize against the same shared baseline. -/
theorem deleted_natural_marked_model
    (f : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (base : Alt ≃* SL) :
    Nonempty (Representation.Equiv
      (externalTensor BinaryPermutation.FiveTensorSquare.δ
        (SL2.BinarySmall.natural.comp f.toMonoidHom))
      (secondSL.comp (base.prodCongr base).toMonoidHom)) := by
  obtain ⟨e⟩ := deleted_natural_marking f
  obtain ⟨b⟩ := second_marked_model base
  exact ⟨e.trans b⟩


/-- The exact displacement-model summands retain the same two-type orbit
under every automorphism, using one common source baseline. -/
theorem marked_model_automorphism_types (base : Alt ≃* SL)
    (a : MulAut (Alt × Alt)) :
    (Nonempty (Representation.Equiv
        ((firstSL.comp (base.prodCongr base).toMonoidHom).comp a.toMonoidHom)
        (firstSL.comp (base.prodCongr base).toMonoidHom)) ∧
      Nonempty (Representation.Equiv
        ((secondSL.comp (base.prodCongr base).toMonoidHom).comp a.toMonoidHom)
        (secondSL.comp (base.prodCongr base).toMonoidHom))) ∨
    (Nonempty (Representation.Equiv
        ((firstSL.comp (base.prodCongr base).toMonoidHom).comp a.toMonoidHom)
        (secondSL.comp (base.prodCongr base).toMonoidHom)) ∧
      Nonempty (Representation.Equiv
        ((secondSL.comp (base.prodCongr base).toMonoidHom).comp a.toMonoidHom)
        (firstSL.comp (base.prodCongr base).toMonoidHom))) := by
  obtain ⟨ef⟩ := first_marked_model base
  obtain ⟨es⟩ := second_marked_model base
  rcases product_automorphism_types a with ⟨⟨f⟩,⟨s⟩⟩ | ⟨⟨f⟩,⟨s⟩⟩
  · exact Or.inl ⟨⟨(compEquiv ef.symm a.toMonoidHom).trans (f.trans ef)⟩,
      ⟨(compEquiv es.symm a.toMonoidHom).trans (s.trans es)⟩⟩
  · exact Or.inr ⟨⟨(compEquiv ef.symm a.toMonoidHom).trans (f.trans es)⟩,
      ⟨(compEquiv es.symm a.toMonoidHom).trans (s.trans ef)⟩⟩

/-- The exact two marked model summands remain distinct under any shared baseline. -/
theorem marked_models_not_equiv (base : Alt ≃* SL) :
    ¬ Nonempty (Representation.Equiv
      (firstSL.comp (base.prodCongr base).toMonoidHom)
      (secondSL.comp (base.prodCongr base).toMonoidHom)) := by
  rintro ⟨e⟩
  obtain ⟨ef⟩ := first_marked_model base
  obtain ⟨es⟩ := second_marked_model base
  exact first_second_not_equiv ⟨ef.trans (e.trans es.symm)⟩

end Representation.AlternatingFiveMovedPair.MixedTypes
