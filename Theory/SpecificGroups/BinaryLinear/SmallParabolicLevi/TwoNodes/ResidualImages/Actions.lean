module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs

/-!
# Rank-one coordinate actions inside a two-node parabolic

The action on either marked block is expressed in the original basis
coefficients. Preserving the cut through that block makes the lower-left
coefficient zero. Over the binary field such a two-dimensional invertible
action has square one: it fixes the first basis vector and either fixes the
second or adds the first to it.

These calculations identify the complementary action of a single-node
parabolic, used for its residual image in Aschbacher–Smith 13.8.25,
combined manuscript of 1 March 2004, printed p.960 (PDF p.977).
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups
noncomputable def nodeLinearAction (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j) :
    flagStabilizer b ({i,j} : Set (Fin 4))ᶜ →* LinearGroup 2 :=
  (linearGroupCongr (nodeCoordinates i j h n hn)).toMonoidHom.comp
    ((Pi.evalMonoidHom _ (pairLabel i j n.castSucc)).comp (flagDiagonalAction b {i,j}ᶜ))

theorem nodeLinearAction_apply (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j)
    (g : flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) (v : Space 2) (r : Fin 2) :
    nodeLinearAction b i j h n hn g v r =
      b.equivFun (g.val (b n.castSucc)) (nodeIndexEquiv i j h n hn r).val * v 0 +
      b.equivFun (g.val (b n.succ)) (nodeIndexEquiv i j h n hn r).val * v 1 := by
  change (nodeCoordinates i j h n hn)
    (flagDiagonalAction b {i,j}ᶜ g (pairLabel i j n.castSucc)
      ((nodeCoordinates i j h n hn).symm v)) r = _
  erw [nodeCoordinates_apply, flagDiagonalAction_apply,
    ← (nodeIndexEquiv i j h n hn).sum_comp]
  simp only [Fin.sum_univ_two, nodeIndexEquiv_zero, nodeIndexEquiv_one]
  have he (s : Fin 2) : (nodeCoordinates i j h n hn).symm v
      (nodeIndexEquiv i j h n hn s) = v s :=
    congrFun ((nodeCoordinates i j h n hn).apply_symm_apply v) s
  rw [he, he]

private theorem flagSpace_coeff_zero (b : FiveBasis) (n : Fin 4) (v : Space 5)
    (hv : v ∈ flagSpace b n) (r : Fin 5) (hr : n.val < r.val) : b.equivFun v r = 0 := by
  have hm := (Module.Basis.mem_span_image b).mp hv
  change ((b.repr v).support : Set (Fin 5)) ⊆ {j : Fin 5 | j.val ≤ n.val} at hm
  by_contra hz
  exact (Nat.not_le_of_gt hr) (hm (Finsupp.mem_support_iff.mpr hz))

theorem nodeLinearAction_entry_zero (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j)
    (g : flagStabilizer b ({i,j} : Set (Fin 4))ᶜ)
    (hg : ∀ v ∈ flagSpace b n, g.val v ∈ flagSpace b n) :
    nodeLinearAction b i j h n hn g ![1,0] 1 = 0 := by
  rw [nodeLinearAction_apply]
  simp only [nodeIndexEquiv_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, add_zero]
  exact flagSpace_coeff_zero b n _
    (hg _ ((basis_mem_flagSpace_iff b n n.castSucc).mpr (by simp))) n.succ (by simp)

private theorem two_vectors (v w : Space 2) (hv : v ≠ 0) (hv1 : v 1 = 0)
    (hw : w ≠ 0) (hwv : w ≠ v) :
    v = ![1,0] ∧ (w = ![0,1] ∨ w = ![1,1]) := by
  have h : ∀ a b c d : ZMod 2, ![a,b] ≠ (0 : Space 2) → b = 0 →
      ![c,d] ≠ (0 : Space 2) → ![c,d] ≠ ![a,b] →
      ![a,b] = ![1,0] ∧ (![c,d] = ![0,1] ∨ ![c,d] = ![1,1]) := by decide +kernel
  have hv' : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  have hw' : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
  simpa only [← hv', ← hw'] using h (v 0) (v 1) (w 0) (w 1) (hv' ▸ hv) hv1 (hw' ▸ hw)
    (by simpa only [← hv', ← hw'] using hwv)

/-- A binary two-dimensional automorphism preserving the first line has square one. -/
theorem linearTwo_square_of_entry_zero (g : LinearGroup 2) (hg : g ![1,0] 1 = 0) :
    g ^ 2 = 1 := by
  have h0 : (![1,0] : Space 2) ≠ 0 := by decide
  have h1 : (![0,1] : Space 2) ≠ 0 := by decide
  have h10 : (![0,1] : Space 2) ≠ ![1,0] := by decide
  obtain ⟨he0, he1⟩ := two_vectors (g ![1,0]) (g ![0,1])
    (fun h => h0 (g.injective (h.trans (map_zero g).symm))) hg
    (fun h => h1 (g.injective (h.trans (map_zero g).symm)))
    (fun h => h10 (g.injective h))
  rw [pow_two]
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 2)).ext
  intro r
  have hb0 : (Pi.basisFun (ZMod 2) (Fin 2)) 0 = ![1,0] := by
    ext s; fin_cases s <;> simp [Pi.basisFun_apply]
  have hb1 : (Pi.basisFun (ZMod 2) (Fin 2)) 1 = ![0,1] := by
    ext s; fin_cases s <;> simp [Pi.basisFun_apply]
  fin_cases r
  · erw [hb0]
    change g (g ![1,0]) = ![1,0]
    rw [he0, he0]
  · erw [hb1]
    change g (g ![0,1]) = ![0,1]
    rcases he1 with he1 | he1
    · rw [he1, he1]
    · rw [he1, show (![1,1] : Space 2) = ![1,0] + ![0,1] by decide, map_add, he0, he1]
      decide

end BinaryLinear.SmallParabolicLevi.TwoNodes

end
