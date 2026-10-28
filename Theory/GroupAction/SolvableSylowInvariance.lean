module

public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow preservation by solvable automorphism groups

Suppose every solvable overgroup of a specified Sylow subgroup P normalizes
P. Then a solvable automorphism group containing the inner image of P
preserves P. Pull the automorphism group back along conjugation; its kernel
is the center, so this pullback is solvable. P is its unique Sylow subgroup,
and every supplied automorphism preserves the pullback and therefore P.

The argument does not require the original group to be centerless. This is
the intrinsic action-transfer step used for Aschbacher--Smith, 15.3.38,
printed p.1136; the model-specific solvable-overgroup theorem is separate.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace MulAut
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Normality in solvable overgroups implies preservation by every element
of a solvable automorphism group containing the inner Sylow image. -/
theorem sylow_map_eq_of_solvable_overgroups (P : Sylow p G)
    (hlocal : ∀ H : Subgroup G, Group.IsSolvable H →
      (P : Subgroup G) ≤ H → H ≤ normalizer (P : Set G))
    (A : Subgroup (MulAut G)) [Group.IsSolvable A]
    (hPA : (P : Subgroup G).map MulAut.conj ≤ A)
    (α : MulAut G) (hα : α ∈ A) :
    (P : Subgroup G).map α.toMonoidHom = P := by
  have hk : (MulAut.conj : G →* MulAut G).ker = center G := by
    ext x
    change MulAut.conj x = 1 ↔ x ∈ center G
    constructor
    · intro hx
      rw [mem_center_iff]
      intro y
      exact (mul_inv_eq_iff_eq_mul.mp (DFunLike.congr_fun hx y)).symm
    · intro hx
      ext y
      change x * y * x⁻¹ = y
      rw [← (mem_center_iff.mp hx) y, mul_inv_cancel_right]
  let : Group.IsSolvable (MulAut.conj : G →* MulAut G).ker := by
    rw [hk]
    infer_instance
  let H := A.comap (MulAut.conj : G →* MulAut G)
  let : Group.IsSolvable H := isSolvable_comap_of_solvable_ker MulAut.conj A
  have hPH : (P : Subgroup G) ≤ H := fun x hx => hPA (mem_map_of_mem _ hx)
  let Q := P.mapSurjective (f := α.toMonoidHom) α.surjective
  have hQH : (Q : Subgroup G) ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    change MulAut.conj (α x) ∈ A
    have he : MulAut.conj (α x) = α * MulAut.conj x * α⁻¹ := by
      ext y
      simp
    rw [he]
    exact A.mul_mem (A.mul_mem hα (hPA (mem_map_of_mem _ hx))) (A.inv_mem hα)
  have hn : (P.subtype hPH).Normal :=
    normal_subgroupOf_of_le_normalizer (hlocal H inferInstance hPH)
  let := Sylow.unique_of_normal (P.subtype hPH) hn
  have he : Q.subtype hQH = P.subtype hPH := Subsingleton.elim _ _
  have hm := congrArg (fun R : Sylow p H => (R : Subgroup H).map H.subtype) he
  change ((Q : Subgroup G).subgroupOf H).map H.subtype =
    ((P : Subgroup G).subgroupOf H).map H.subtype at hm
  have hQP : (Q : Subgroup G) = P := by
    simpa only [subgroupOf_map_subtype, inf_eq_left.mpr hQH, inf_eq_left.mpr hPH] using hm
  exact hQP

end MulAut
