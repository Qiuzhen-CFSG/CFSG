module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Coordinates
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Dimensions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.BigOperators.Pi

/-!
# All hyperplanes in the degree-eight disjoint-swap group

Binary coordinates identify `D` with a four-dimensional vector space. A proper
subspace lies in the kernel of a nonzero linear form; maximality makes this an
equality. The sixteen-word tables give order eight for each nonzero form kernel,
and permutation sign identifies the even part with the all-ones form.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(5),(6), printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight
open Representation.BinaryOffender

/-- The coefficients of a binary linear form, in binary word order. -/
def hyperplaneCoeffs (m : Fin 16) : Fin 4 → ZMod 2 :=
  (finFunctionFinEquiv (m := 2) (n := 4)).symm m

/-- The linear form whose coefficients are the bits of `m`. -/
def hyperplaneForm (m : Fin 16) : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, hyperplaneCoeffs m i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_left_comm]

/-- The kernel inside the binary coordinate group. -/
def hyperplaneBinary (m : Fin 16) : Subgroup BinaryFour where
  carrier := {x | hyperplaneForm m (Multiplicative.toAdd x) = 0}
  one_mem' := map_zero _
  mul_mem' := by intro x y hx hy; change hyperplaneForm m (x.toAdd + y.toAdd) = 0; rw [map_add, hx, hy, add_zero]
  inv_mem' := by intro x hx; change hyperplaneForm m (-x.toAdd) = 0; rw [map_neg, hx, neg_zero]

/-- The subgroup cut out by a binary linear form on the four swap coordinates. -/
def hyperplaneKernel (m : Fin 16) : Subgroup Perm :=
  (hyperplaneBinary m).map binaryPermutation

/-- All eight words in a nonzero form's kernel, used for fixed-vector counting. -/
def hyperplaneGenerators (m : Fin 16) : Finset Perm :=
  (Finset.univ.filter (fun j : Fin 16 => hyperplaneForm m (hyperplaneCoeffs j) = 0)).image dWords

/-- Number of nonzero coefficients of the form. -/
def hyperplaneWeight (m : Fin 16) : ℕ :=
  (Finset.univ.filter (fun i => hyperplaneCoeffs m i ≠ 0)).card

theorem mem_hyperplaneKernel (m : Fin 16) (g : Perm) :
    g ∈ hyperplaneKernel m ↔ ∃ j, hyperplaneForm m (hyperplaneCoeffs j) = 0 ∧ dWords j = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨finFunctionFinEquiv x.toAdd, ?_, rfl⟩
    change hyperplaneForm m ((finFunctionFinEquiv (m := 2) (n := 4)).symm
      ((finFunctionFinEquiv (m := 2) (n := 4)) x.toAdd)) = 0
    exact (congrArg (fun y : Fin 4 → ZMod 2 => hyperplaneForm m y)
      ((finFunctionFinEquiv (m := 2) (n := 4)).symm_apply_apply x.toAdd)).trans hx
  · rintro ⟨j, hj, rfl⟩
    refine ⟨Multiplicative.ofAdd (hyperplaneCoeffs j), hj, ?_⟩
    change dWords ((finFunctionFinEquiv (m := 2) (n := 4))
      ((finFunctionFinEquiv (m := 2) (n := 4)).symm j)) = dWords j
    rw [Equiv.apply_symm_apply]

theorem hyperplaneKernel_closure (m : Fin 16) :
    hyperplaneKernel m = Subgroup.closure (hyperplaneGenerators m : Set Perm) := by
  have he : (hyperplaneGenerators m : Set Perm) = (hyperplaneKernel m : Set Perm) := by
    ext g
    change g ∈ hyperplaneGenerators m ↔ g ∈ hyperplaneKernel m
    simp only [hyperplaneGenerators, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, mem_hyperplaneKernel]
  rw [he, Subgroup.closure_eq]

theorem hyperplaneKernel_le_D (m : Fin 16) : hyperplaneKernel m ≤ D 8 := by
  intro g hg
  obtain ⟨j, _, rfl⟩ := (mem_hyperplaneKernel m g).mp hg
  exact (mem_D_iff _).mpr ⟨j, rfl⟩

theorem card_hyperplaneKernel (m : Fin 16) (hm : m ≠ 0) :
    Nat.card (hyperplaneKernel m) = 8 := by
  let e : {j : Fin 16 // hyperplaneForm m (hyperplaneCoeffs j) = 0} ≃ hyperplaneKernel m :=
    Equiv.ofBijective (fun j => ⟨dWords j.val, (mem_hyperplaneKernel m _).mpr ⟨j.val, j.property, rfl⟩⟩)
      ⟨fun a b h => Subtype.ext (dWords_injective (congrArg Subtype.val h)), by
        intro g
        obtain ⟨j, hj, he⟩ := (mem_hyperplaneKernel m g.val).mp g.property
        exact ⟨⟨j, hj⟩, Subtype.ext he⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  revert hm
  revert m
  decide +kernel

theorem rank_hyperplaneKernel (m : Fin 16) (hm : m ≠ 0) :
    rank (hyperplaneKernel m) = 3 :=
  rank_eq_of_card_eq_two_pow (card_hyperplaneKernel m hm)

theorem hyperplaneKernel_lt_D (m : Fin 16) (hm : m ≠ 0) :
    hyperplaneKernel m < D 8 := by
  refine lt_of_le_of_ne (hyperplaneKernel_le_D m) ?_
  intro h
  have hr := rank_hyperplaneKernel m hm
  rw [h, rank_D] at hr
  contradiction

private def hyperplanePreimage (H : Subgroup Perm) : Submodule (ZMod 2) (Fin 4 → ZMod 2) where
  carrier := {x | binaryPermutation (Multiplicative.ofAdd x) ∈ H}
  zero_mem' := by change binaryPermutation 1 ∈ H; simp
  add_mem' := by
    intro x y hx hy
    change binaryPermutation (Multiplicative.ofAdd x * Multiplicative.ofAdd y) ∈ H
    rw [map_mul]
    exact H.mul_mem hx hy
  smul_mem' := by
    intro a x hx
    have ha : a = 0 ∨ a = 1 := by revert a; decide +kernel
    rcases ha with rfl | rfl
    · change binaryPermutation (Multiplicative.ofAdd (0 • x)) ∈ H
      simp
    · simpa using hx

theorem hyperplane_eq_kernel {H : Subgroup Perm} (hH : H ⋖ D 8) :
    ∃ m : Fin 16, m ≠ 0 ∧ H = hyperplaneKernel m := by
  have hp : hyperplanePreimage H < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro he
    have hd : D 8 ≤ H := by
      intro g hg
      obtain ⟨x, rfl⟩ := (show g ∈ binaryPermutation.range by rw [binaryPermutation_range]; exact hg)
      have hx : x.toAdd ∈ hyperplanePreimage H := by rw [he]; trivial
      exact hx
    exact hH.lt.not_ge hd
  obtain ⟨f, hf, hpf⟩ := (hyperplanePreimage H).exists_le_ker_of_lt_top hp
  let c : Fin 4 → ZMod 2 := fun i => f (Pi.single i 1)
  let m : Fin 16 := finFunctionFinEquiv c
  have hfm : f = hyperplaneForm m := by
    apply LinearMap.ext
    intro x
    have he := congrArg f (pi_eq_sum_univ' x)
    have hcoeff : hyperplaneCoeffs m = c :=
      (finFunctionFinEquiv (m := 2) (n := 4)).symm_apply_apply c
    change f x = ∑ i, hyperplaneCoeffs m i * x i
    rw [hcoeff]
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm, c] using he
  have hm : m ≠ 0 := by
    intro hm
    apply hf
    rw [hfm, hm]
    have hz : hyperplaneCoeffs 0 = 0 := by decide +kernel
    apply LinearMap.ext
    intro x
    change (∑ i, hyperplaneCoeffs 0 i * x i) = 0
    simp [hz]
  refine ⟨m, hm, ?_⟩
  have hle : H ≤ hyperplaneKernel m := by
    intro g hg
    obtain ⟨x, hx⟩ := (show g ∈ binaryPermutation.range by rw [binaryPermutation_range]; exact hH.le hg)
    refine ⟨x, ?_, hx⟩
    change hyperplaneForm m x.toAdd = 0
    rw [← hfm]
    apply hpf
    change binaryPermutation x ∈ H
    simpa [hx] using hg
  exact ((hH.eq_or_eq hle (hyperplaneKernel_le_D m)).resolve_right
    (hyperplaneKernel_lt_D m hm).ne).symm

theorem isElementaryTwo_hyperplaneKernel (m : Fin 16) (hm : m ≠ 0) :
    IsElementaryTwo (hyperplaneKernel m) := by
  apply isElementaryTwo_D8.of_le (hyperplaneKernel_le_D m)
  intro h
  have hr := rank_hyperplaneKernel m hm
  rw [h, Representation.BinaryOffender.rank_bot] at hr
  contradiction

theorem hyperplaneKernel_covBy (m : Fin 16) (hm : m ≠ 0) :
    hyperplaneKernel m ⋖ D 8 := by
  refine ⟨hyperplaneKernel_lt_D m hm, ?_⟩
  intro K hK hKD
  have hd₁ := Subgroup.card_dvd_of_le hK.le
  have hd₂ := Subgroup.card_dvd_of_le hKD.le
  rw [card_hyperplaneKernel m hm] at hd₁
  have hcD : Nat.card (D 8) = 16 := card_disjointTranspositions 4
  rw [hcD] at hd₂
  have hchoices : Nat.card K = 8 ∨ Nat.card K = 16 := by
    have : Nat.card K ≤ 16 := Nat.le_of_dvd (by decide) hd₂
    have hp : 0 < Nat.card K := Nat.pos_of_ne_zero (by intro h; simp [h] at hd₂)
    obtain ⟨k, hk⟩ := hd₁
    omega
  rcases hchoices with hc | hc
  · exact hK.ne (Subgroup.eq_of_le_of_card_ge hK.le (by rw [hc, card_hyperplaneKernel m hm]))
  · exact hKD.ne (Subgroup.eq_of_le_of_card_ge hKD.le (by rw [hcD, hc]))

/-- Every hyperplane, and only a hyperplane, is a nonzero binary form kernel. -/
theorem hyperplane_iff_kernel (H : Subgroup Perm) :
    H ⋖ D 8 ↔ ∃ m : Fin 16, m ≠ 0 ∧ H = hyperplaneKernel m := by
  constructor
  · exact hyperplane_eq_kernel
  · rintro ⟨m, hm, rfl⟩
    exact hyperplaneKernel_covBy m hm

/-- The alternating part is the all-four-coordinates parity kernel. -/
theorem evenPart_eq_hyperplaneKernel : evenPart 8 = hyperplaneKernel 15 := by
  have ht : ∀ j : Fin 16, Equiv.Perm.sign (dWords j) = 1 ↔
      hyperplaneForm 15 (hyperplaneCoeffs j) = 0 := by decide +kernel
  ext g
  change (g ∈ D 8 ∧ Equiv.Perm.sign g = 1) ↔ g ∈ hyperplaneKernel 15
  rw [mem_hyperplaneKernel]
  constructor
  · rintro ⟨hg, hs⟩
    obtain ⟨j, rfl⟩ := (mem_D_iff g).mp hg
    exact ⟨j, (ht j).mp hs, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(mem_D_iff _).mpr ⟨j, rfl⟩, (ht j).mpr hj⟩

theorem hyperplaneWeight_evenPart : hyperplaneWeight 15 = 4 := by decide +kernel

theorem hyperplaneWeight_bounds (m : Fin 16) (hm : m ≠ 0) :
    1 ≤ hyperplaneWeight m ∧ hyperplaneWeight m ≤ 4 := by
  revert hm m
  decide +kernel

theorem dWords_mem_hyperplaneKernel (m j : Fin 16) :
    dWords j ∈ hyperplaneKernel m ↔ hyperplaneForm m (hyperplaneCoeffs j) = 0 := by
  rw [mem_hyperplaneKernel]
  constructor
  · rintro ⟨k, hk, he⟩
    simpa only [dWords_injective he] using hk
  · intro hj
    exact ⟨j, hj, rfl⟩

/-- Binary forms are uniquely determined by their kernels over the two-element field. -/
theorem hyperplaneKernel_injective : Function.Injective hyperplaneKernel := by
  have ht : ∀ m n : Fin 16,
      (∀ j : Fin 16, hyperplaneForm m (hyperplaneCoeffs j) = 0 ↔
        hyperplaneForm n (hyperplaneCoeffs j) = 0) → m = n := by decide +kernel
  intro m n h
  apply ht m n
  intro j
  rw [← dWords_mem_hyperplaneKernel, ← dWords_mem_hyperplaneKernel, h]

theorem hyperplaneWeight_four_iff (m : Fin 16) : hyperplaneWeight m = 4 ↔ m = 15 := by
  revert m
  decide +kernel

/-- A nonzero binary mask represents a genuinely nonzero linear form. -/
theorem hyperplaneForm_eq_zero_iff (m : Fin 16) : hyperplaneForm m = 0 ↔ m = 0 := by
  have ht : ∀ n : Fin 16,
      (∀ j : Fin 16, hyperplaneForm n (hyperplaneCoeffs j) = 0) ↔ n = 0 := by
    decide +kernel
  constructor
  · intro h
    apply (ht m).mp
    intro j
    rw [h]
    rfl
  · rintro rfl
    apply LinearMap.ext
    decide +kernel

/-- The even part is itself one of the hyperplanes of `D`. -/
theorem evenPart_covBy_D : evenPart 8 ⋖ D 8 := by
  rw [evenPart_eq_hyperplaneKernel]
  exact hyperplaneKernel_covBy 15 (by decide)

end CFSG.Quasithin.ChapterB.Offenders.Eight
