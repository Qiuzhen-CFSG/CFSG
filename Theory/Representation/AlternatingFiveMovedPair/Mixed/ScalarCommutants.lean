module
public import Theory.Representation.AlternatingFiveMovedPair.Mixed
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The scalar commutants separating the two binary A₅ modules

Transitivity on the fifteen nonzero natural vectors forces invariant subspaces
to be zero or the whole space. The cubic fixed-vector obstruction then rules
out any nonzero intertwiner between the natural and deleted four-spaces.
The individual commutants are respectively F₄ and F₂. These facts feed the
literal mixed tensor-pair centralizer in the D.3.5 moved-orbit estimate.
Source: Aschbacher–Smith, D.3.5, printed pp.195–196.
-/
@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Mixed
open SL2FourNatural SL2FourNatural.SemilinearNormalizer
abbrev ν : Representation (ZMod 2) SL Natural :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp SL2FourNatural.action
abbrev δ : Representation (ZMod 2) SL Deleted := deletedAction.comp specialFiveLines

private lemma natural_invariant (P : Submodule (ZMod 2) Natural)
    (hP : ∀ g : SL, ∀ v ∈ P, ν g v ∈ P) : P = ⊥ ∨ P = ⊤ := by
  by_cases h : P = ⊥
  · exact Or.inl h
  right
  obtain ⟨v, hv, hv0⟩ := P.ne_bot_iff.mp h
  apply eq_top_iff.mpr
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ P.zero_mem
  obtain ⟨g, hg⟩ := transitive_nonzero v w hv0 hw
  rw [← hg]
  exact hP g v hv

private lemma no_deleted_natural_injection (f : Deleted →ₗ[ZMod 2] Natural)
    (hi : Function.Injective f) (hf : ∀ g : SL, ∀ v, f (δ g v) = ν g (f v)) : False := by
  apply BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_natural_injection
    alternatingFiveEquiv.symm.toMonoidHom alternatingFiveEquiv.symm.injective
    f.toAddMonoidHom hi
  intro a v
  have ha : specialFiveLines (alternatingFiveEquiv.symm a) = a.val :=
    congrArg Subtype.val (alternatingFiveEquiv.apply_symm_apply a)
  change f (deletedAction a.val v) = ν (alternatingFiveEquiv.symm a) (f v)
  simpa only [δ, MonoidHom.comp_apply, ha] using hf (alternatingFiveEquiv.symm a) v

lemma deleted_to_natural_zero (f : Deleted →ₗ[ZMod 2] Natural)
    (hf : ∀ g : SL, ∀ v, f (δ g v) = ν g (f v)) : f = 0 := by
  have hr : ∀ g : SL, ∀ v ∈ f.range, ν g v ∈ f.range := by
    rintro g _ ⟨v,rfl⟩
    exact ⟨δ g v, hf g v⟩
  rcases natural_invariant f.range hr with h | h
  · exact LinearMap.range_eq_bot.mp h
  · have hs : Function.Surjective f := LinearMap.range_eq_top.mp h
    have hi : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (finrank_deleted.trans finrank_natural.symm)).mpr hs
    exact (no_deleted_natural_injection f hi hf).elim

lemma natural_to_deleted_zero (f : Natural →ₗ[ZMod 2] Deleted)
    (hf : ∀ g : SL, ∀ v, f (ν g v) = δ g (f v)) : f = 0 := by
  have hk : ∀ g : SL, ∀ v ∈ f.ker, ν g v ∈ f.ker := by
    intro g v hv
    change f (ν g v) = 0
    rw [hf, show f v = 0 from hv, map_zero]
  rcases natural_invariant f.ker hk with h | h
  · have hi := LinearMap.ker_eq_bot.mp h
    let e := LinearMap.linearEquivOfInjective f hi (finrank_natural.trans finrank_deleted.symm)
    apply (no_deleted_natural_injection e.symm.toLinearMap e.symm.injective ?_).elim
    intro g v
    apply e.injective
    change e (e.symm (δ g v)) = e (ν g (e.symm v))
    rw [e.apply_symm_apply]
    change δ g v = f (ν g (e.symm v))
    rw [hf]
    change δ g v = δ g (e (e.symm v))
    rw [e.apply_symm_apply]
  · apply LinearMap.ext
    intro v
    have hv : v ∈ f.ker := by rw [h]; exact Submodule.mem_top
    exact hv

lemma deleted_commuting_scalar (f : Deleted →ₗ[ZMod 2] Deleted)
    (hf : ∀ g : SL, ∀ v, f (δ g v) = δ g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  have he (p : Sym) (v : BinaryPermutation.core (Fin 5)) :
      e (BinaryPermutation.coreRepresentation (Fin 5) p v) = deletedAction p (e v) :=
    BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) p v
  let t := e.symm.toLinearMap.comp (f.comp e.toLinearMap)
  have ht (a : alternatingGroup (Fin 5)) (v : BinaryPermutation.core (Fin 5)) :
      t (BinaryPermutation.alternatingCoreRepresentation (Fin 5) a v) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) a (t v) := by
    apply e.injective
    change e (e.symm (f (e (BinaryPermutation.coreRepresentation (Fin 5) a.val v)))) = _
    rw [e.apply_symm_apply, he]
    have ha : specialFiveLines (alternatingFiveEquiv.symm a) = a.val :=
      congrArg Subtype.val (alternatingFiveEquiv.apply_symm_apply a)
    have hh := hf (alternatingFiveEquiv.symm a) (e v)
    simp only [δ, MonoidHom.comp_apply, ha] at hh
    rw [hh]
    change deletedAction a.val (f (e v)) = e (BinaryPermutation.coreRepresentation (Fin 5) a.val (t v))
    rw [he]
    simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply]
  obtain ⟨c,hc⟩ := BinaryPermutation.FiveTensorNormalizer.core_commuting_scalar t ht
  refine ⟨c, ?_⟩
  intro v
  have h := congrArg e (hc (e.symm v))
  simpa only [t, LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply,
    map_smul, e.apply_symm_apply] using h

lemma natural_commuting_scalar (f : Natural →ₗ[ZMod 2] Natural)
    (hf : ∀ g : SL, ∀ v, f (ν g v) = ν g (f v)) :
    ∃ c : F, ∀ v, f v = c • v :=
  SL2NaturalOffenders.centralizer_scalar f.toAddMonoidHom hf
end Representation.AlternatingFiveMovedPair.Mixed
