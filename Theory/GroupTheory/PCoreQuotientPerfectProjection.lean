module

public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreImage
/-!
# The canonical component quotient of a perfect normalizing group

Let a perfect group J contain and normalize I. If I/O₂(I) is centerless
with soluble outer automorphism group, the action of J on I/O₂(I) is inner.
The unique implementing element gives a homomorphism J → I/O₂(I). It
restricts to the original quotient map on I and is equivariant for every
element normalizing both I and J.

This constructs the component projection used on the one- or two-component
Suzuki orbit in Aschbacher--Smith 11.5.6(3), printed p.781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] {I J : Subgroup G}
variable [Group.IsPerfect J]

/-- A perfect normalizing overgroup projects equivariantly to the centerless quotient. -/
theorem exists_perfect_coreQuotient_projection
    (hIJ : I ≤ J) (hJI : J ≤ normalizer (I : Set G))
    [Group.IsSolvable (MulAut.Outer (I ⧸ pCore 2 I))]
    (hz : center (I ⧸ pCore 2 I) = ⊥) :
    ∃ f : J →* (I ⧸ pCore 2 I),
      (∀ i : I, f (inclusion hIJ i) = QuotientGroup.mk' (pCore 2 I) i) ∧
      ∀ (x : normalizer (J : Set G)) (hx : (x : G) ∈ normalizer (I : Set G)) (j : J),
        f (J.normalizerMonoidHom x j) =
          quotientAut (pCore 2 I) (I.normalizerMonoidHom ⟨x, hx⟩) (f j) := by
  let aN : normalizer (I : Set G) →* MulAut (I ⧸ pCore 2 I) :=
    (quotientAut (pCore 2 I)).comp I.normalizerMonoidHom
  let a : J →* MulAut (I ⧸ pCore 2 I) := aN.comp (inclusion hJI)
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  obtain ⟨k, _, hk⟩ := MulAut.perfect_subgroup_exists_inner_lift a.range hz
  let f := k.comp a.rangeRestrict
  have hf (j : J) : MulAut.conj (f j) = a j := hk (a.rangeRestrict j)
  have hi := conj_injective_of_center_eq_bot hz
  refine ⟨f, ?_, ?_⟩
  · intro i
    apply hi
    rw [hf]
    apply MulEquiv.ext
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 I) z
    change quotientAut (pCore 2 I) (I.normalizerMonoidHom
      (inclusion hJI (inclusion hIJ i))) (QuotientGroup.mk' (pCore 2 I) y) = _
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 I) (i * y * i⁻¹) = _
    simp only [map_mul, map_inv, MulAut.conj_apply]
  · intro x hx j
    let α := aN ⟨x,hx⟩
    apply hi
    rw [hf]
    have hj : inclusion hJI (J.normalizerMonoidHom x j) =
        (⟨x,hx⟩ : normalizer (I : Set G)) * inclusion hJI j * ⟨x,hx⟩⁻¹ := rfl
    change aN (inclusion hJI (J.normalizerMonoidHom x j)) = MulAut.conj (α (f j))
    rw [hj, map_mul, map_mul, map_inv]
    change α * a j * α⁻¹ = MulAut.conj (α (f j))
    rw [← hf]
    apply MulEquiv.ext
    intro z
    change α (f j * α.symm z * (f j)⁻¹) = α (f j) * z * (α (f j))⁻¹
    simp only [map_mul, map_inv, α.apply_symm_apply]
end Subgroup
