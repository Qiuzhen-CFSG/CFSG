module

public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry

/-!
# Abelian root subgroups and the Suzuki ovoid

A root element commuting with its conjugate by a nonidentity split-torus
element has first coordinate zero: the twisted commutation relation would
otherwise force the torus parameter to be fixed by the Tits automorphism,
hence to equal one. An element swapping infinity and zero cannot carry a
nonidentity translate by such a root element to another such translate.
The latter follows directly from the third homogeneous coordinate.

These are the coordinate ingredients of the subgroup argument in
Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), and Suzuki (1962).
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII
open scoped LinearAlgebra.Projectivization

/-- Commutation with a nontrivial torus conjugate forces the first root coordinate to vanish. -/
public theorem suzukiRootGL_first_eq_zero_of_commute_conjugate (m : ℕ) (a b : BinaryGaloisField (2 * m + 1))
    (t : (BinaryGaloisField (2 * m + 1))ˣ) (ht : t ≠ 1)
    (h : Commute (SuzukiRootGL m a b)
      (SuzukiTorusGL m t * SuzukiRootGL m a b * (SuzukiTorusGL m t)⁻¹)) : a = 0 := by
  rw [BenderSuzuki.External.suzukiTorusGL_conj_root m (suzukiTits m)
    (suzukiTits_sq m) (suzukiTits_apply m)] at h
  have hh := congrArg (fun M : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
    (M : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) 0 2) h.eq
  simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four] at hh
  by_contra ha
  have hta : suzukiTits m (t : BinaryGaloisField (2 * m + 1)) = t := by
    apply mul_right_cancel₀ (mul_ne_zero ha ((map_ne_zero (suzukiTits m)).2 ha))
    simp only [mul_pow, ← suzukiTits_apply] at hh
    linear_combination hh
  have hsq : (t : BinaryGaloisField (2 * m + 1)) ^ 2 = t := by
    rw [← suzukiTits_sq, hta, hta]
  apply ht
  apply Units.ext
  apply mul_left_cancel₀ t.ne_zero
  simpa only [pow_two, Units.val_one, mul_one] using hsq

/-- A swap of the standard pair cannot preserve nonidentity root translates with first coordinate zero. -/
public theorem suzukiOvoid_swap_root_first_zero (m : ℕ) (g r s : SuzukiMatrixGroup m)
    (hgi : g • suzukiOvoidInfinity m = suzukiOvoidZero m)
    (hgz : g • suzukiOvoidZero m = suzukiOvoidInfinity m)
    (b d : BinaryGaloisField (2 * m + 1))
    (hr : r.val = SuzukiRootGL m 0 b)
    (hs : s.val = SuzukiRootGL m 0 d)
    (h : g • (r • suzukiOvoidZero m) = s • suzukiOvoidZero m) : r = 1 := by
  have ht : g * suzukiWeyl m ∈ SuzukiSplitTorus m := by
    rw [mem_suzukiSplitTorus_iff_fix_pair]
    simp only [mul_smul, suzukiWeyl_smul_infinity, suzukiWeyl_smul_zero, hgi, hgz,
      and_self]
  obtain ⟨t, ht⟩ := (mem_suzukiSplitTorus_iff m _).mp ht
  have hg : g.val = SuzukiTorusGL m t * SuzukiWeylGL m := by
    have hh := congrArg (fun z : SuzukiMatrixGroup m => z.val)
      (show g = (g * suzukiWeyl m) * suzukiWeyl m by
        rw [mul_assoc, suzukiWeyl_sq, mul_one])
    change g.val = (g * suzukiWeyl m).val * SuzukiWeylGL m at hh
    rw [ht] at hh
    exact hh
  have hv := congrArg Subtype.val h
  change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv •
    ((Matrix.GeneralLinearGroup.toLin r.val).toLinearEquiv • (suzukiOvoidZero m).val) =
    (Matrix.GeneralLinearGroup.toLin s.val).toLinearEquiv • (suzukiOvoidZero m).val at hv
  rw [hg, hr, hs] at hv
  simp only [suzukiOvoidZero, Projectivization.smul_mk] at hv
  rw [Projectivization.mk_eq_mk_iff] at hv
  obtain ⟨c, hc⟩ := hv
  have hc2 := congrFun hc (2 : Fin 4)
  simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiTorusGL, SuzukiTorusMatrix,
    SuzukiWeylGL, SuzukiWeylMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hc2
  apply Subtype.ext
  change r.val = 1
  rw [hr, hc2, BenderSuzuki.External.suzukiRootGL_zero_zero]

end BenderSuzuki.MatrixGroups
