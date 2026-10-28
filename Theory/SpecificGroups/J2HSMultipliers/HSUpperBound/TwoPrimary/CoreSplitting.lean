module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.CoreSplitting.Pairing
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.LocalReduction

/-!
# Splitting over the actual HS normalizer core

Every surjective central extension of the literal HS elementary-eight
normalizer splits over its C₄³ two-core. The inverse image is abelian by
the invariant commutator-pairing calculation. For a lifted actor d, the
homomorphism x ↦ x / (dxd⁻¹) kills the central kernel and descends to the
core. Its induced map is bijective because the checked order-seven actor
has no nonidentity fixed point. Composing with that inverse gives the section.

This proves more than the finite perfect central two-cover contract: the
upper group and kernel need no finiteness, perfectness or prime restriction.
The final theorem applies the section to the exact restriction map used by
`not_four_dvd_of_core_section_of_local_bound`. The independent local-kernel
bound remains explicit; the HS multiplier assembly belongs to the parent.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 Table 5.3m.
Only independently checked model geometry is used from the configuration
on Aschbacher–Smith printed p.412.
-/

open Subgroup MonoidHom
open scoped IsMulCommutative
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting

private theorem exists_section_of_abelian_preimage {D N : Type*} [Group D] [Group N]
    (Q : Subgroup N) [Q.Normal] [Finite Q] [IsMulCommutative Q]
    (g : D →* N) (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    [IsMulCommutative (Q.comap g)]
    (y : N) (hy : FixedPointFree (MulAut.conjNormal (H := Q) y)) :
    ∃ s : Q →* D, g.comp s = Q.subtype := by
  obtain ⟨d, hd⟩ := hg y
  let P := Q.comap g
  let φ : MulAut P := MulAut.conjNormal d
  let δ : P →* P := (MonoidHom.id P) / φ.toMonoidHom
  let ε : Q →* Q := (MonoidHom.id Q) / (MulAut.conjNormal y).toMonoidHom
  let f : P →* Q := g.subgroupComap Q
  have hf : Function.Surjective f := g.subgroupComap_surjective_of_surjective Q hg
  have hker : f.ker ≤ δ.ker := by
    intro x hx
    have hxg : g x = 1 := congrArg Subtype.val (show f x = 1 from hx)
    have hxc := Subgroup.mem_center_iff.mp (hk hxg) d
    change x / φ x = 1
    apply div_eq_one.mpr
    apply Subtype.ext
    change (x : D) = d * x * d⁻¹
    rw [hxc, mul_inv_cancel_right]
  let t : Q →* P := f.liftOfSurjective hf ⟨δ, hker⟩
  have ht (x : P) : t (f x) = δ x :=
    f.liftOfRightInverse_comp_apply (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨δ, hker⟩ x
  have hmap (x : P) : f (δ x) = ε (f x) := by
    apply Subtype.ext
    change g ((x : D) / (d * x * d⁻¹)) = g x / (y * g x * y⁻¹)
    simp only [map_div, map_mul, map_inv, hd]
  have htmap (q : Q) : f (t q) = ε q := by
    obtain ⟨x, rfl⟩ := hf q
    rw [ht, hmap]
  let e : Q ≃* Q := MulEquiv.ofBijective ε
    ⟨hy.commutatorMap_injective, hy.commutatorMap_surjective⟩
  refine ⟨P.subtype.comp (t.comp e.symm.toMonoidHom), ?_⟩
  ext q
  change (f (t (e.symm q)) : N) = q
  rw [htmap]
  exact congrArg Subtype.val (e.apply_symm_apply q)

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting
open Subgroup
open Sporadic.LeechRelated.HS BlockNormalizer BlockNormalizer.CoreGeometry

/-- Every surjective central extension of the literal HS elementary-eight
normalizer splits over its actual C₄³ two-core. -/
public theorem exists_core_section {D : Type*} [Group D]
    (g : D →* baseNormalizer) (hg : Function.Surjective g)
    (hk : g.ker ≤ center D) :
    ∃ s : pCore 2 baseNormalizer →* D,
      g.comp s = (pCore 2 baseNormalizer).subtype := by
  let := core_preimage_isMulCommutative g hg hk
  obtain ⟨y, _, hy⟩ := exists_seven_fixedPointFree
  exact exists_section_of_abelian_preimage (pCore 2 baseNormalizer) g hg hk y hy

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
open Subgroup
open Sporadic.LeechRelated.HS EvenLocalCandidates BlockNormalizer
universe u

/-- The core-section premise of the two-primary HS reduction is discharged.
The split-involution local-kernel bound is the remaining independent input. -/
public theorem not_four_dvd_of_local_bound
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hp : IsPGroup 2 f.ker)
    (hlocal : ∀ (D : Type u) [Group D] [Finite D] [Group.IsPerfect D]
      (g : D →* baseNormalizer), Function.Surjective g →
      g.ker ≤ center D → IsPGroup 2 g.ker →
      (∃ s : pCore 2 baseNormalizer →* D, g.comp s = (pCore 2 baseNormalizer).subtype) →
      (∃ x : D, g x = normalizerInvolution ∧ x ^ 2 = 1) →
      Nat.card g.ker ≤ 2) : ¬ 4 ∣ Nat.card f.ker := by
  apply not_four_dvd_of_core_section_of_local_bound f hf hk hp
    (CoreSplitting.exists_core_section (f.subgroupComap baseNormalizer)
      (f.subgroupComap_surjective_of_surjective baseNormalizer hf)
      (restriction_ker_le_center f hk)) hlocal

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
