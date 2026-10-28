module

public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Odd-order elements centralizing binary transvections

In dimension at least four, a transvection acts on two coordinates and fixes
a complementary binary plane. The product of the two opposite transvections
on that plane has order three. Conjugacy of binary transvections transfers
this element to the centralizer of any rank-one displacement. Perfectness
of the binary linear group places it in the derived subgroup.

This is the intrinsic linear-group exclusion used in Aschbacher–Smith,
combined manuscript (1 March 2004), the split-constituent paragraph of
15.3.58, printed p.1149, after G.6.4, printed pp.345–346. It does not require
order or simplicity certification for the linear groups.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.TransvectionCubicCentralizer
open OuterCyclic

private def root {n : ℕ} (i j : Fin n) (h : i ≠ j) : BinaryLinear.GL (Fin n → ZMod 2) :=
  transvection (Pi.single i 1) (LinearMap.proj j) (by simp [h.symm])

private theorem root_apply {n : ℕ} (i j : Fin n) (h : i ≠ j)
    (v : Fin n → ZMod 2) (k : Fin n) :
    root i j h v k = v k + if k = i then v j else 0 := by
  change v k + v j * (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k = _
  by_cases hk : k = i <;> simp [hk]

private theorem root_transvection {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    IsTransvection (root i j h) := by
  refine ⟨Pi.single i 1, LinearMap.proj j, ?_, ?_, _, rfl⟩
  · intro hz
    have := congrFun hz i
    simp at this
  · intro hz
    have := LinearMap.congr_fun hz (Pi.single j 1)
    simp at this

private theorem standard_cubic {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ x : BinaryLinear.GL (Fin n → ZMod 2), orderOf x = 3 ∧ Commute x (root a b hab) := by
  let x := root c d hcd * root d c hcd.symm
  have hx : x ^ 3 = 1 := by
    ext v k
    change x (x (x v)) k = v k
    dsimp only [x, LinearEquiv.mul_apply]
    simp only [root_apply]
    by_cases hkc : k = c
    · subst k
      simp [hcd, hcd.symm]
      ring_nf
      simp only [show (13 : ZMod 2) = 1 by decide, show (8 : ZMod 2) = 0 by decide,
        mul_one, mul_zero, add_zero]
    · by_cases hkd : k = d
      · subst k
        simp [hcd, hcd.symm]
        ring_nf
        simp only [show (5 : ZMod 2) = 1 by decide, show (8 : ZMod 2) = 0 by decide,
          mul_one, mul_zero, add_zero]
      · simp [hkc, hkd]
  have hx1 : x ≠ 1 := by
    intro he
    have hh := congrArg (fun g : BinaryLinear.GL (Fin n → ZMod 2) => g (Pi.single c 1) d) he
    simp [x, LinearEquiv.mul_apply, root_apply, hcd.symm] at hh
  refine ⟨x, orderOf_eq_prime hx hx1, ?_⟩
  apply LinearEquiv.ext
  intro v
  funext k
  simp only [x, LinearEquiv.mul_apply, root_apply]
  by_cases hka : k = a
  · subst k
    simp [hac, had, hbc, hbd]
  · by_cases hkc : k = c
    · subst k
      simp [hac.symm, had.symm, hcd]
    · by_cases hkd : k = d
      · subst k
        simp [had.symm, hac.symm, hcd.symm]
      · simp [hka, hkc, hkd]

private theorem isTransvection_of_rank_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (t : BinaryLinear.GL V)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1) :
    IsTransvection t := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr.le
  have hact (w : V) : t w = w + f w • v := LinearMap.congr_fun he w
  have hne : t.toLinearMap ≠ LinearMap.id := by
    intro h
    rw [h, sub_self, LinearMap.range_zero] at hr
    have hz : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) = 0 := finrank_bot _ _
    omega
  have hf : f ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hv : v ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with h | h
    · exact h
    · have htv : t v = 0 := by
        rw [hact, h, one_smul, ZModModule.add_self]
      exact (hv (t.map_eq_zero_iff.mp htv)).elim
  exact ⟨v, f, hv, hf, hfv, LinearEquiv.ext hact⟩

/-- A transvection in binary dimension at least four centralizes an element
of order three in the derived subgroup. -/
theorem exists_order_three_mem_commutator_commute {n : ℕ} (hn : 4 ≤ n)
    (t : BinaryLinear.GL (Fin n → ZMod 2))
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1) :
    ∃ c ∈ commutator (BinaryLinear.GL (Fin n → ZMod 2)), orderOf c = 3 ∧ Commute c t := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  obtain ⟨x, hx, hxs⟩ := standard_cubic a b c d hab
    (by simp [a, c, Fin.ext_iff]) (by simp [a, d, Fin.ext_iff])
    (by simp [b, c, Fin.ext_iff]) (by simp [b, d, Fin.ext_iff])
    (by simp [c, d, Fin.ext_iff])
  obtain ⟨g, hg⟩ := transvections_conjugate (root_transvection a b hab)
    (isTransvection_of_rank_one t hr)
  let : Group.IsPerfect (LinearGroup n) := linearGroup_isPerfect n (by omega)
  refine ⟨MulAut.conj g x, Group.IsPerfect.mem_commutator,
    ((MulAut.conj g).orderOf_eq x).trans hx, ?_⟩
  have hc : Commute (MulAut.conj g x) (MulAut.conj g (root a b hab)) :=
    hxs.map (MulAut.conj g).toMonoidHom
  exact hg ▸ hc

end BinaryLinear.TransvectionCubicCentralizer
