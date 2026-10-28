module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.Reduction

/-!
# The B₂ main-parameter product

For a positive B₂ block with long root α and short root β, the main word is
`xα(t) xβ(f(t)) x(α+β)(t*f(t))`, where `f` is the half-Frobenius. Collecting
the words at 1 and u gives the main word at `1 + u` times
`x(α+2β)(u) x(α+β)(f(u))`, exactly the central word at u.

The mixed-length commutation hypothesis does not assert commutation of the
two short roots β and α+β. We derive it from the actual B₂ swap relation:
all root generators are involutions, and the two commuting top-root factors
make its correction an involution. Taking inverses of the swap shows that
this correction commutes with the β-factor. Its long-root factor already
commutes with β, so its short-root factor does too. Choosing the long
parameter as `c / b` covers every short-root pair when `b ≠ 0`; the zero
case is immediate. Root-curve additivity then completes the collection.

The result remains conditional on a positive geometric layout and the two
block relations, which the parent's independent inputs discharge. It uses
no generation, fixed factorization, normal generation, or perfectness.
The calculation also applies to the binary coefficient field at `m = 0`.

Source: GLS3 Table 2.4, type V, in `refs/KGroup/GLS3/chapter2.tex`:
`x(t,0) x(t',0) = x(t+t', t^(2θ)*t')`, specialized to `t = 1`.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RadicalCoordinates RadicalCoordinates.FixedCoordinates

/-- An involutory correction in a swap of involutions commutes with the
second factor. This is the characteristic-two collection step. -/
private theorem correction_commute {G : Type*} [Group G] (A B C : G)
    (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1)
    (h : B * A = A * B * C) : Commute B C := by
  have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_left hA
  have hBi : B⁻¹ = B := inv_eq_of_mul_eq_one_left hB
  have hCi : C⁻¹ = C := inv_eq_of_mul_eq_one_left hC
  have hi := congrArg Inv.inv h
  simp only [mul_inv_rev, hAi, hBi, hCi] at hi
  have h₁ := congrArg (fun x => A * x) h
  have h₂ := congrArg (fun x => x * A) hi
  simp only [← mul_assoc, hA, one_mul] at h₁
  simp only [mul_assoc, hA, mul_one] at h₂
  exact h₁.symm.trans (by simpa only [mul_assoc] using h₂)

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem root_add (m : ℕ) (r : F4Chevalley.Root) (a b : CoefficientField m) :
    rootGeneratorInGroup m r (a + b) =
      rootGeneratorInGroup m r a * rootGeneratorInGroup m r b :=
  Subtype.ext (F4Chevalley.rootCurve_add r a b)

private theorem root_mul_self (m : ℕ) (r : F4Chevalley.Root) (a : CoefficientField m) :
    rootGeneratorInGroup m r a * rootGeneratorInGroup m r a = 1 := by
  rw [← root_add, CharTwo.add_self_eq_zero, root_zero]

namespace RootWordLayout
variable (L : RootWordLayout .positive)

private theorem quartet_short_length (j : Fin (quartetCount .positive)) :
    IsShortRoot (L.blocks.roots (.inr (j, 1))).val := by
  rw [← L.blocks.quartet_dual_zero]
  exact (exceptionalRootPermutation_long_iff _).mp (L.blocks.quartet_long j)

private theorem quartet_high_long (j : Fin (quartetCount .positive)) :
    IsLongRoot (L.blocks.roots (.inr (j, 3))).val := by
  rw [← L.blocks.quartet_dual_two]
  exact (exceptionalRootPermutation_short_iff _).mp (L.blocks.quartet_short_two j)

private theorem quartet_long_mixed_commute (m : ℕ) (hc : MixedRootCommutation m)
    (j : Fin (quartetCount .positive)) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m (longRoot (L.quartetIndex j)) a)
      (rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) b) := by
  have hd : 0 ≤ dot (L.blocks.roots (.inr (j, 0))).val.val
      (L.blocks.roots (.inr (j, 2))).val.val := by
    rw [L.blocks.quartet_add]
    change 0 ≤ _ ⬝ᵥ (_ + _)
    rw [dotProduct_add]
    change 0 ≤ dot _ _ + dot _ _
    rw [isLongRoot_norm _ (L.blocks.quartet_long j), L.blocks.quartet_dot]
    norm_num
  have h := hc _ _ (L.blocks.roots (.inr (j, 0))).property
    (L.blocks.roots (.inr (j, 2))).property (L.blocks.quartet_long j)
    (L.blocks.quartet_short_two j) hd a b
  simpa only [L.quartet_long, L.quartet_mixed] using h

private theorem quartet_high_short_commute (m : ℕ) (hc : MixedRootCommutation m)
    (j : Fin (quartetCount .positive)) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m (highRoot (L.quartetIndex j)) a)
      (rootGeneratorInGroup m (shortRoot (L.quartetIndex j)) b) := by
  have hd : 0 ≤ dot (L.blocks.roots (.inr (j, 3))).val.val
      (L.blocks.roots (.inr (j, 1))).val.val := by
    rw [L.blocks.quartet_add_two]
    change 0 ≤ (_ + (2 : ℝ) • _) ⬝ᵥ _
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    change 0 ≤ dot _ _ + 2 * dot _ _
    rw [L.blocks.quartet_dot, isShortRoot_norm _ (L.quartet_short_length j)]
    norm_num
  have h := hc _ _ (L.blocks.roots (.inr (j, 3))).property
    (L.blocks.roots (.inr (j, 1))).property (L.quartet_high_long j)
    (L.quartet_short_length j) hd a b
  simpa only [L.quartet_high, L.quartet_short] using h

private theorem quartet_swap (m : ℕ) (hs : B2RootSwap m)
    (j : Fin (quartetCount .positive)) (a b : CoefficientField m) :
    rootGeneratorInGroup m (shortRoot (L.quartetIndex j)) b *
        rootGeneratorInGroup m (longRoot (L.quartetIndex j)) a =
      rootGeneratorInGroup m (longRoot (L.quartetIndex j)) a *
        rootGeneratorInGroup m (shortRoot (L.quartetIndex j)) b *
        rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) (a * b) *
        rootGeneratorInGroup m (highRoot (L.quartetIndex j)) (a * b ^ 2) := by
  have h := hs _ _ _ _ (L.blocks.roots (.inr (j, 0))).property
    (L.blocks.roots (.inr (j, 1))).property (L.blocks.quartet_long j)
    (L.quartet_short_length j) (L.blocks.quartet_dot j) (L.blocks.quartet_add j)
    (L.blocks.quartet_add_two j) a b
  simpa only [L.quartet_long, L.quartet_short, L.quartet_mixed, L.quartet_high] using h

/-- The two short-root curves in a B₂ quartet commute in characteristic two.
The swap correction is an involution; cancelling its commuting high-root
factor proves the assertion, with the long parameter chosen as `c / b`. -/
theorem quartet_short_mixed_commute (m : ℕ) (hc : MixedRootCommutation m)
    (hs : B2RootSwap m) (j : Fin (quartetCount .positive)) (b c : CoefficientField m) :
    Commute (rootGeneratorInGroup m (shortRoot (L.quartetIndex j)) b)
      (rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) c) := by
  by_cases hb : b = 0
  · subst b
    rw [root_zero]
    exact Commute.one_left _
  have hw := L.quartet_swap m hs j (c / b) b
  rw [div_mul_cancel₀ _ hb] at hw
  have hCD := (L.quartet_top_commute m hc j ((c / b) * b ^ 2) c).symm
  have hE :
      (rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) c *
        rootGeneratorInGroup m (highRoot (L.quartetIndex j)) ((c / b) * b ^ 2)) *
      (rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) c *
        rootGeneratorInGroup m (highRoot (L.quartetIndex j)) ((c / b) * b ^ 2)) = 1 := by
    rw [hCD.symm.mul_mul_mul_comm, root_mul_self, root_mul_self, one_mul]
  have h := correction_commute _ _ _ (root_mul_self m _ _) (root_mul_self m _ _) hE
    (by simpa only [mul_assoc] using hw)
  have hBD := (L.quartet_high_short_commute m hc j ((c / b) * b ^ 2) b).symm
  simpa only [mul_assoc, root_mul_self, mul_one] using h.mul_right hBD

private theorem quartet_mainParameterProduct (m : ℕ) (hc : MixedRootCommutation m)
    (hs : B2RootSwap m) (j : Fin (quartetCount .positive)) (u : CoefficientField m) :
    rootWord m (L.quartetIndex j) 1 * rootWord m (L.quartetIndex j) u =
      rootWord m (L.quartetIndex j) (1 + u) * centralWord m (L.quartetIndex j) u := by
  let A := rootGeneratorInGroup m (longRoot (L.quartetIndex j))
  let B := rootGeneratorInGroup m (shortRoot (L.quartetIndex j))
  let C := rootGeneratorInGroup m (mixedRoot (L.quartetIndex j))
  let D := rootGeneratorInGroup m (highRoot (L.quartetIndex j))
  let f := halfFrobenius m
  have hA (a b) : A (a + b) = A a * A b := root_add m _ a b
  have hB (a b) : B (a + b) = B a * B b := root_add m _ a b
  have hC (a b) : C (a + b) = C a * C b := root_add m _ a b
  have hAC (a b) : Commute (A a) (C b) := L.quartet_long_mixed_commute m hc j a b
  have hBC (a b) : Commute (B a) (C b) := L.quartet_short_mixed_commute m hc hs j a b
  have hDB (a b) : Commute (D a) (B b) := L.quartet_high_short_commute m hc j a b
  have hDC (a b) : Commute (D a) (C b) := L.quartet_top_commute m hc j a b
  have hw : B 1 * A u = A u * B 1 * C u * D u := by
    simpa only [one_pow, mul_one] using L.quartet_swap m hs j u 1
  have hrest : Commute (C u * D u * C 1) (B (f u)) :=
    (((hBC (f u) u).symm.mul_left (hDB u (f u))).mul_left (hBC (f u) 1).symm)
  have hscalar : (1 + u) * (1 + f u) + f u = 1 + u + u * f u := by
    calc
      (1 + u) * (1 + f u) + f u = 1 + u + u * f u + (f u + f u) := by ring
      _ = 1 + u + u * f u := by rw [CharTwo.add_self_eq_zero, add_zero]
  simp only [rootWord, centralWord, L.quartet_even, ite_true, L.quartet_fieldEnd,
    map_one, one_mul, map_add]
  change (A 1 * B 1 * C 1) * (A u * B (f u) * C (u * f u)) =
    (A (1 + u) * B (1 + f u) * C ((1 + u) * (1 + f u))) * (D u * C (f u))
  calc
    (A 1 * B 1 * C 1) * (A u * B (f u) * C (u * f u)) =
        A 1 * B 1 * (C 1 * A u) * B (f u) * C (u * f u) := by
      simp only [mul_assoc]
    _ = A 1 * (B 1 * A u) * C 1 * B (f u) * C (u * f u) := by
      rw [(hAC u 1).symm.eq]
      simp only [mul_assoc]
    _ = (A 1 * A u) * (B 1 * (C u * D u * C 1) * B (f u)) * C (u * f u) := by
      rw [hw]
      simp only [mul_assoc]
    _ = A (1 + u) * (B (1 + f u) * (C u * D u * C 1)) * C (u * f u) := by
      rw [hrest.right_comm, ← hA, ← hB]
    _ = A (1 + u) * B (1 + f u) * D u * C (1 + u + u * f u) := by
      rw [(hDC u u).symm.eq, hC (1 + u) (u * f u)]
      rw [show C (1 + u) = C u * C 1 by rw [add_comm (1 : CoefficientField m) u, hC]]
      simp only [mul_assoc]
    _ = (A (1 + u) * B (1 + f u) * C ((1 + u) * (1 + f u))) * (D u * C (f u)) := by
      rw [← hscalar, hC]
      exact (hDC u ((1 + u) * (1 + f u))).mul_mul_mul_comm _ _

end RootWordLayout

/-- GLS3 Table 2.4, type V, at first main parameter 1. The geometric layout
and the mixed-length and B₂ swap relations suffice; no generation or fixed
factorization hypothesis is used. The identity holds for every `m`, hence
in particular for the source applications with `1 ≤ m`. -/
theorem mainParameterProduct_of_block_relations (m : ℕ) (L : RootWordLayout .positive)
    (hc : MixedRootCommutation m) (hs : B2RootSwap m) : MainParameterProduct m := by
  intro i hi u
  obtain ⟨j, hj⟩ | ⟨j, rfl⟩ := L.positive_covers i
  · exact (L.pair_odd j (hj.symm ▸ hi)).elim
  · exact L.quartet_mainParameterProduct m hc hs j u

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
