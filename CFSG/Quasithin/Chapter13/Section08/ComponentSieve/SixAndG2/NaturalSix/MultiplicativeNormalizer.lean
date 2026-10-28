module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import Theory.Representation.BinaryPermutationMulAction
public import Mathlib.Algebra.Module.ZMod

/-!
# Multiplicative automorphisms of the natural six-letter module

Over the prime field, every additive automorphism is linear. The resulting
identification of multiplicative automorphisms with invertible linear maps
carries the literal symmetric and alternating natural actions to their
existing linear images. Transporting the proved linear normalizer equality
therefore identifies the full multiplicative normalizer with the same S₆
image, without changing the natural-module marking.

Source application: Aschbacher–Smith, 14.3.19(10); the natural module is the
augmentation quotient of §B.3. The linear normalizer calculation is the
one used in 13.8.26–27, printed pp.962–963.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

private noncomputable def multiplicativeLinearHom :
    LinearGroup →* MulAut (Multiplicative Natural) where
  toFun u := (LinearMap.GeneralLinearGroup.toLinearEquiv u).toAddEquiv.toMultiplicative
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private theorem multiplicativeLinearHom_injective : Function.Injective multiplicativeLinearHom := by
  intro u v h
  apply Units.ext
  apply LinearMap.ext
  intro x
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h (Multiplicative.ofAdd x))

private theorem multiplicativeLinearHom_surjective : Function.Surjective multiplicativeLinearHom := by
  intro u
  let a : Natural ≃+ Natural := AddEquiv.toMultiplicative.symm u
  let e := LinearEquiv.ofBijective (a.toAddMonoidHom.toZModLinearMap 2) a.bijective
  refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv e, ?_⟩
  ext x
  rfl

private noncomputable def multiplicativeLinearEquiv :
    LinearGroup ≃* MulAut (Multiplicative Natural) :=
  MulEquiv.ofBijective multiplicativeLinearHom
    ⟨multiplicativeLinearHom_injective, multiplicativeLinearHom_surjective⟩

private theorem multiplicativeLinearEquiv_comp :
    multiplicativeLinearEquiv.toMonoidHom.comp symmetricHom =
      BinaryPermutation.naturalMulAction (Fin 6) := by
  ext g x
  rfl

private theorem map_symmetricImage_multiplicative :
    symmetricImage.map multiplicativeLinearEquiv.toMonoidHom =
      (BinaryPermutation.naturalMulAction (Fin 6)).range := by
  rw [symmetricImage, MonoidHom.map_range, multiplicativeLinearEquiv_comp]

private theorem map_alternatingImage_multiplicative :
    alternatingImage.map multiplicativeLinearEquiv.toMonoidHom =
      ((BinaryPermutation.naturalMulAction (Fin 6)).comp
        (alternatingGroup (Fin 6)).subtype).range := by
  rw [alternatingImage, MonoidHom.map_range, alternatingHom_eq_comp,
    ← MonoidHom.comp_assoc, multiplicativeLinearEquiv_comp]

/-- The full normalizer of the literal natural A₆ action is its literal S₆ image. -/
theorem normalizer_alternatingMulImage :
    Subgroup.normalizer (((BinaryPermutation.naturalMulAction (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype).range : Set (MulAut (Multiplicative Natural))) =
      (BinaryPermutation.naturalMulAction (Fin 6)).range := by
  rw [← map_alternatingImage_multiplicative, ← Subgroup.map_equiv_normalizer_eq,
    normalizer_alternatingImage, map_symmetricImage_multiplicative]

/-- A normalizing automorphism is induced by an actual permutation of the same six letters. -/
theorem exists_permutation_of_normalizes_alternatingMulImage
    (u : MulAut (Multiplicative Natural))
    (hu : u ∈ Subgroup.normalizer (((BinaryPermutation.naturalMulAction (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype).range : Set (MulAut (Multiplicative Natural)))) :
    ∃ g : Equiv.Perm (Fin 6), BinaryPermutation.naturalMulAction (Fin 6) g = u := by
  rw [normalizer_alternatingMulImage] at hu
  exact hu

/-- The original natural-module marking extends to every automorphism normalizing
its actual alternating actor. This consumes the group and module equivalences
with the same pointwise convention as source 14.3.19(4). -/
theorem marked_normalizing_automorphism
    {W : Type*} [Group W] (P : Subgroup (MulAut W))
    (e : P ≃* alternatingGroup (Fin 6)) (q : W ≃* Multiplicative Natural)
    (hq : ∀ (p : P) (w : W), (q (p.val w)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (e p).val (q w).toAdd)
    (u : MulAut W) (hu : u ∈ Subgroup.normalizer (P : Set (MulAut W))) :
    ∃ g : Equiv.Perm (Fin 6), ∀ w : W, (q (u w)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g (q w).toAdd := by
  have he (p : P) : MulAut.congr q p.val =
      BinaryPermutation.naturalMulAction (Fin 6) (e p).val := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change (q (p.val (q.symm v))).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (e p).val v.toAdd
    rw [hq, q.apply_symm_apply]
  have hP : P.map (MulAut.congr q).toMonoidHom =
      ((BinaryPermutation.naturalMulAction (Fin 6)).comp
        (alternatingGroup (Fin 6)).subtype).range := by
    ext a
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨e ⟨p,hp⟩, (he ⟨p,hp⟩).symm⟩
    · rintro ⟨p,rfl⟩
      refine ⟨(e.symm p).val, (e.symm p).property, ?_⟩
      change MulAut.congr q (e.symm p).val =
        BinaryPermutation.naturalMulAction (Fin 6) p.val
      rw [he, e.apply_symm_apply]
  have hu' := Subgroup.mem_map_of_mem (MulAut.congr q).toMonoidHom hu
  rw [Subgroup.map_equiv_normalizer_eq, hP] at hu'
  obtain ⟨g,hg⟩ := exists_permutation_of_normalizes_alternatingMulImage _ hu'
  refine ⟨g, fun w => ?_⟩
  have hh := congrArg Multiplicative.toAdd (DFunLike.congr_fun hg (q w)).symm
  change (q (u (q.symm (q w)))).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 6) g (q w).toAdd at hh
  simpa only [q.symm_apply_apply] using hh


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
