module

public import FeitThompson.BGsection3.Defs
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Abelian images of Frobenius kernels

Every homomorphism from a finite Frobenius group to an abelian group kills
the Frobenius kernel. A nonidentity complement element acts without fixed
points on the kernel; its commutator map is therefore a permutation of the
kernel. Every kernel element is consequently a commutator.

This elementary Frobenius-group fact is used to place a subgroup's
Frobenius kernel inside the root group of a Suzuki Borel; compare
Huppert--Blackburn, *Finite Groups III*, XI.3.12(e).
-/

namespace IsFrobeniusGroupWithKernelComplement

/-- An abelian image of a finite Frobenius group kills its kernel. -/
public theorem le_ker_of_isMulCommutative
    {G A : Type*} [Group G] [Finite G] [Group A] [IsMulCommutative A]
    {F D : Subgroup G} (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (f : G →* A) : F ≤ f.ker := by
  let : F.Normal := hFrob.normal
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hFrob.complement_ne_bot
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  let φ : F →* F := (MulAut.conjNormal (d : G)).toMonoidHom
  have hfixed : MonoidHom.FixedPointFree φ := by
    intro x hx
    apply Subtype.ext
    by_contra hxne
    have hxD : (x : G) ∉ D := fun h =>
      hxne (Subgroup.disjoint_def.mp hFrob.isComplement'.disjoint x.property h)
    have hcomm : (d : G) * (x : G) = (x : G) * (d : G) := by
      have heq : (d : G) * (x : G) * (d : G)⁻¹ = (x : G) :=
        congrArg Subtype.val hx
      exact mul_inv_eq_iff_eq_mul.mp heq
    have hdconj : (d : G) ∈ D.conjBy (x : G) := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨d, d.property, ?_⟩
      change (x : G) * (d : G) * (x : G)⁻¹ = (d : G)
      rw [← hcomm]
      simp [mul_assoc]
    exact hd (Subtype.ext
      (Subgroup.disjoint_def.mp (hFrob.disjoint_conjBy (x : G) hxD) d.property hdconj))
  intro x hx
  obtain ⟨y, hy⟩ := hfixed.commutatorMap_surjective (⟨x, hx⟩ : F)
  have heq : (y : G) / ((d : G) * (y : G) * (d : G)⁻¹) = x :=
    congrArg Subtype.val hy
  change f x = 1
  rw [← heq, map_div, map_mul, map_mul, map_inv]
  rw [mul_comm' (f (d : G)) (f (y : G))]
  simp [mul_assoc]

end IsFrobeniusGroupWithKernelComplement
