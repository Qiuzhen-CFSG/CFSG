module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Displacement of actors moving the Schur algebra

Let L act irreducibly on V and let t normalize L. If t does not commute
with every L-endomorphism, it moves at least half the dimension of V.
Indeed, choose f not commuting with t. The difference t f t⁻¹ - f is a
nonzero L-endomorphism, hence injective by Schur's lemma. On the t-fixed
space it agrees with (t - 1) f, giving an injection into the moved space.
Rank-nullity proves the bound without a semilinear basis or a field choice.

The endomorphism algebra is the actual Schur algebra: Mathlib's
`IntertwiningMap.equivAlgEnd` identifies it with End_{k[L]}(V). Over a finite
field and in finite dimension it is the Schur field. This supplies the
scalar-moving case in Guralnick--Malle, Classification of 2F-modules II,
§3.5 and Proposition 6.2, used by Aschbacher--Smith K.3.4, printed p.456.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (L : Subgroup G)

/-- Commutation with the actual component endomorphism algebra. -/
def IsSchurLinear (t : G) : Prop :=
  ∀ f : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype),
    Commute (ρ t) f.toLinearMap

/-- Every component element is linear over its own endomorphism algebra. -/
theorem isSchurLinear_of_mem {t : G} (ht : t ∈ L) : IsSchurLinear ρ L t := by
  intro f
  exact (f.isIntertwining' ⟨t, ht⟩).symm

private def conjugateComponentEnd (t : G)
    (ht : t ∈ (Subgroup.normalizer (L : Set G)))
    (f : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype)) :
    IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype) where
  toLinearMap := ρ t * f.toLinearMap * ρ t⁻¹
  isIntertwining' g := by
    let g' : L := ⟨t⁻¹ * g * t, by
      simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).inv_mem ht) g).mp g.property⟩
    have hm : (g' : G) = t⁻¹ * g * t := rfl
    ext v
    change ρ t (f (ρ t⁻¹ (ρ g v))) = ρ g (ρ t (f (ρ t⁻¹ v)))
    have hmove : ρ t⁻¹ (ρ g v) = ρ (g' : G) (ρ t⁻¹ v) := by
      simp only [hm, map_mul, Module.End.mul_apply]
      simp
    rw [hmove]
    change ρ t (f ((ρ.comp L.subtype) g' (ρ t⁻¹ v))) = _
    rw [f.isIntertwining]
    change ρ t (ρ (g' : G) (f (ρ t⁻¹ v))) = _
    simp only [hm, map_mul, Module.End.mul_apply]
    simp

variable [FiniteDimensional k V] [IsIrreducible (ρ.comp L.subtype)]

/-- An actor moving the component Schur algebra displaces at least half the module. -/
theorem finrank_le_twice_displacement_of_not_isSchurLinear
    (t : G) (ht : t ∈ (Subgroup.normalizer (L : Set G))) (hnot : ¬ IsSchurLinear ρ L t) :
    Module.finrank k V ≤ 2 * Module.finrank k (LinearMap.range (ρ t - 1)) := by
  classical
  obtain ⟨f, hf⟩ := not_forall.mp hnot
  let f' := conjugateComponentEnd ρ L t ht f
  have hne : f' - f ≠ 0 := by
    intro hz
    have he : f' = f := sub_eq_zero.mp hz
    apply hf
    show ρ t * f.toLinearMap = f.toLinearMap * ρ t
    have he' := congrArg IntertwiningMap.toLinearMap he
    change ρ t * f.toLinearMap * ρ t⁻¹ = f.toLinearMap at he'
    have hh := congrArg (fun q : Module.End k V => q * ρ t) he'
    simpa only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] using hh
  have hinj : Function.Injective (f' - f) :=
    (IsIrreducible.injective_or_eq_zero (f' - f)).resolve_right hne
  let C := LinearMap.ker (ρ t - 1)
  let j : C →ₗ[k] LinearMap.range (ρ t - 1) :=
    ((ρ t - 1).rangeRestrict.comp f.toLinearMap).comp C.subtype
  have hfix (v : C) : ρ t v = v := sub_eq_zero.mp v.property
  have hinv (v : C) : ρ t⁻¹ v = v := by
    have hh := congrArg (ρ t⁻¹) (hfix v)
    simpa using hh.symm
  have hj (v : C) : (j v : V) = (f' - f) v := by
    change ρ t (f v) - f v = ρ t (f (ρ t⁻¹ v)) - f v
    rw [hinv]
  have hjinj : Function.Injective j := by
    intro v w hvw
    apply Subtype.ext
    apply hinj
    simpa only [← hj] using congrArg Subtype.val hvw
  have hd := LinearMap.finrank_le_finrank_of_injective hjinj
  have hr := (ρ t - 1).finrank_range_add_finrank_ker
  change Module.finrank k (LinearMap.ker (ρ t - 1)) ≤ _ at hd
  omega

end Representation
