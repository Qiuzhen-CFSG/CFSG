module

public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# The scalar blocks of an amplified deleted A₅ module

A homogeneous sum of deleted five-letter modules is represented by a function
into the binary augmentation core. Every block of an A₅-equivariant linear map
is a binary scalar, since the simple core has absolute scalar commutant. Removing
the permutation part of an intertwiner therefore permits arbitrary mixing of
the multiplicity coordinates, with the same mixing on each core coordinate.

Source: Aschbacher--Smith D.3.9 and D.3.21, printed pp.199--201 and 204--207.
-/

@[expose] public section

namespace Representation.AlternatingFive.AmplifiedDeleted

abbrev C := BinaryPermutation.core (Fin 5)
abbrev Alt := alternatingGroup (Fin 5)
abbrev Sym := Equiv.Perm (Fin 5)

/-- The literal pointwise deleted-module action, with arbitrary multiplicity. -/
def deletedSumAction (ι : Type*) : Representation (ZMod 2) Sym (ι → C) where
  toFun g := LinearMap.pi fun i =>
    (BinaryPermutation.coreRepresentation (Fin 5) g).comp (LinearMap.proj i)
  map_one' := by ext v i; simp
  map_mul' g h := by ext v i; simp

@[simp] theorem deletedSumAction_apply {ι : Type*} (g : Sym) (v : ι → C) (i : ι) :
    deletedSumAction ι g v i = BinaryPermutation.coreRepresentation (Fin 5) g (v i) := rfl

/-- All blocks of a commuting endomorphism are binary scalars. -/
theorem sum_commuting_blocks {ι : Type*} [Fintype ι]
    (T : Module.End (ZMod 2) (ι → C))
    (hT : ∀ (g : Alt) v,
      T (deletedSumAction ι g.val v) = deletedSumAction ι g.val (T v)) :
    ∃ a : ι → ι → ZMod 2, ∀ v i, (T v) i = ∑ j, a i j • v j := by
  classical
  have hblock (i j : ι) : ∃ a : ZMod 2, ∀ v : C,
      T (Pi.single j v) i = a • v := by
    let f : C →ₗ[ZMod 2] C :=
      (LinearMap.proj i).comp (T.comp (LinearMap.single (ZMod 2) (fun _ : ι => C) j))
    apply BinaryPermutation.FiveTensorNormalizer.core_commuting_scalar f
    intro g v
    have hs : Pi.single j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) g v) =
        deletedSumAction ι g.val (Pi.single j v) := by
      ext k
      by_cases hk : k = j
      · subst k; simp
      · simp [Pi.single_eq_of_ne hk]
    change T (Pi.single j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) g v)) i = _
    rw [hs, hT]
    rfl
  choose a ha using hblock
  refine ⟨a, fun v i => ?_⟩
  have hv : v = ∑ j, Pi.single j (v j) := by ext j; simp
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [Finset.sum_apply, ha]

/-- Removing the displayed S₅ automorphism leaves scalar multiplicity blocks. -/
theorem sum_intertwining_blocks {ι : Type*} [Fintype ι]
    (T : Module.End (ZMod 2) (ι → C)) (p : Sym)
    (hT : ∀ (g : Alt) v, T (deletedSumAction ι g.val v) =
      deletedSumAction ι (p * g.val * p⁻¹) (T v)) :
    ∃ a : ι → ι → ZMod 2, ∀ v i,
      (T v) i = BinaryPermutation.coreRepresentation (Fin 5) p (∑ j, a i j • v j) := by
  let S := (deletedSumAction ι p⁻¹).comp T
  have hS (g : Alt) (v : ι → C) :
      S (deletedSumAction ι g.val v) = deletedSumAction ι g.val (S v) := by
    change deletedSumAction ι p⁻¹ (T (deletedSumAction ι g.val v)) =
      deletedSumAction ι g.val (deletedSumAction ι p⁻¹ (T v))
    rw [hT]
    have hp : p⁻¹ * (p * g.val * p⁻¹) = g.val * p⁻¹ := by group
    simpa only [map_mul, Module.End.mul_apply] using
      congrArg (fun s => deletedSumAction ι s (T v)) hp
  obtain ⟨a, ha⟩ := sum_commuting_blocks S hS
  refine ⟨a, fun v i => ?_⟩
  have he := congrArg (BinaryPermutation.coreRepresentation (Fin 5) p) (ha v i)
  change BinaryPermutation.coreRepresentation (Fin 5) p
    (BinaryPermutation.coreRepresentation (Fin 5) p⁻¹ ((T v) i)) = _ at he
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using he

end Representation.AlternatingFive.AmplifiedDeleted
