module
public import Theory.SpecificGroups.Suzuki.RootOmega

/-!
# Square fibers in a Suzuki root group

For the Tits automorphism θ, the identity θ(aθ(a)) = a(aθ(a)) makes
 a ↦ aθ(a) injective, hence bijective over the finite Suzuki field.
Together with u(a,b)² = u(0,aθ(a)), this identifies the square fibers
with center cosets and shows that every central element is a square.
These are identities in the actual matrix root group.

Source: Huppert--Blackburn III, XI.3.1; GLS4, Chapter 2, Lemma 14.7(b).
-/

noncomputable section
namespace BenderSuzuki.MatrixGroups
open Subgroup PFAppendixIII

private theorem tits_norm_injective (m : ℕ) :
    Function.Injective (fun a : BinaryGaloisField (2 * m + 1) => a * suzukiTits m a) := by
  intro a b hab
  change a * suzukiTits m a = b * suzukiTits m b at hab
  have hn (x : BinaryGaloisField (2 * m + 1)) :
      suzukiTits m (x * suzukiTits m x) = x * (x * suzukiTits m x) := by
    rw [map_mul, suzukiTits_sq]
    ring
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := (mul_eq_zero.mp (show b * suzukiTits m b = 0 by simpa only [zero_mul] using hab.symm)).elim id
      (fun h => (suzukiTits m).injective (by simpa using h))
    exact hb.symm
  · apply mul_right_cancel₀ (mul_ne_zero ha ((map_ne_zero (suzukiTits m)).mpr ha))
    calc
      a * (a * suzukiTits m a) = suzukiTits m (a * suzukiTits m a) := (hn a).symm
      _ = suzukiTits m (b * suzukiTits m b) := congrArg (suzukiTits m) hab
      _ = b * (a * suzukiTits m a) := by rw [hn, hab]

private def rootPoint (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    SuzukiRootSubgroup m :=
  ⟨⟨SuzukiRootGL m a b, suzukiRootClosure_le m (subset_closure ⟨a, b, rfl⟩)⟩,
    subset_closure ⟨a, b, rfl⟩⟩

private theorem rootPoint_mul (m : ℕ) (hm : 0 < m)
    (a b c d : BinaryGaloisField (2 * m + 1)) :
    rootPoint m a b * rootPoint m c d =
      rootPoint m (a + c) (b + d + a * suzukiTits m c) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (External.huppert_blackburn_XI_3_1 m hm (suzukiTits m)
    (suzukiTits_sq m)).2.2.2.2.2.2.2.2.1 a b c d

private theorem rootPoint_sq (m : ℕ) (hm : 0 < m)
    (a b : BinaryGaloisField (2 * m + 1)) :
    rootPoint m a b ^ 2 = rootPoint m 0 (a * suzukiTits m a) := by
  simp only [pow_two, rootPoint_mul m hm, CharTwo.add_self_eq_zero, zero_add]

private theorem rootPoint_zero (m : ℕ) : rootPoint m 0 0 = 1 :=
  Subtype.ext (Subtype.ext (External.suzukiRootGL_zero_zero m))

private theorem rootPoint_surjective (m : ℕ) (x : SuzukiRootSubgroup m) :
    ∃ a b, x = rootPoint m a b := by
  obtain ⟨a, b, h⟩ := (mem_suzukiRootSubgroup_iff m x.val).mp x.property
  exact ⟨a, b, Subtype.ext (Subtype.ext h)⟩

/-- The square fibers of the Suzuki root group are exactly the cosets of its center. -/
public theorem suzukiRootSubgroup_square_eq_iff (m : ℕ) (hm : 0 < m)
    (x y : SuzukiRootSubgroup m) :
    x ^ 2 = y ^ 2 ↔ x⁻¹ * y ∈ center (SuzukiRootSubgroup m) := by
  constructor
  · intro hs
    obtain ⟨a, b, rfl⟩ := rootPoint_surjective m x
    obtain ⟨c, d, rfl⟩ := rootPoint_surjective m y
    rw [rootPoint_sq m hm, rootPoint_sq m hm] at hs
    have hac : a = c := tits_norm_injective m
      (congrArg (fun z : SuzukiRootSubgroup m => z.val.val (0 : Fin 4) (2 : Fin 4)) hs)
    subst c
    have he : rootPoint m a b * rootPoint m 0 (b + d) = rootPoint m a d := by
      rw [rootPoint_mul m hm]
      simp only [add_zero, map_zero, mul_zero]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [← he, inv_mul_cancel_left]
    apply (suzukiRootSubgroup_square_iff_center m hm _).mp
    rw [rootPoint_sq m hm]
    simpa only [map_zero, zero_mul] using rootPoint_zero m
  · intro hz
    have hcomm : Commute x (x⁻¹ * y) := (mem_center_iff.mp hz x)
    have hsq := (suzukiRootSubgroup_square_iff_center m hm _).mpr hz
    have hh := hcomm.mul_pow 2
    simpa only [mul_inv_cancel_left, inv_mul_cancel_left, hsq, mul_one] using hh.symm

/-- Squares in the root group belong to its center. -/
public theorem suzukiRootSubgroup_square_mem_center (m : ℕ) (hm : 0 < m)
    (x : SuzukiRootSubgroup m) : x ^ 2 ∈ center (SuzukiRootSubgroup m) := by
  apply (suzukiRootSubgroup_square_iff_center m hm _).mp
  simpa only [← pow_mul] using suzukiRootSubgroup_pow_four m hm x

/-- Every central element of the Suzuki root group is a square in that root group. -/
public theorem suzukiRootSubgroup_square_surjective (m : ℕ) (hm : 0 < m)
    (z : center (SuzukiRootSubgroup m)) :
    ∃ x : SuzukiRootSubgroup m, x ^ 2 = z.val := by
  obtain ⟨a, b, he⟩ := rootPoint_surjective m z.val
  have hz := (suzukiRootSubgroup_square_iff_center m hm z.val).mpr z.property
  rw [he, rootPoint_sq m hm] at hz
  have hn : a * suzukiTits m a = 0 := by
    exact congrArg (fun w : SuzukiRootSubgroup m => w.val.val (0 : Fin 4) (2 : Fin 4)) hz
  have ha : a = 0 := (mul_eq_zero.mp hn).elim id
    (fun h => (suzukiTits m).injective (by simpa using h))
  obtain ⟨c, hc⟩ := (Finite.surjective_of_injective (tits_norm_injective m)) b
  change c * suzukiTits m c = b at hc
  refine ⟨rootPoint m c 0, ?_⟩
  rw [rootPoint_sq m hm, hc, he, ha]

end BenderSuzuki.MatrixGroups
