module
public import Theory.Representation.UniformBinaryPolarQuotient
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Singular radicals of the binary five- and nine-point spaces

A quadratic form vanishing on the coordinate vectors evaluates on their
sum as the number of unordered pairs. For degrees five and nine that
number is even. The uniform polar radical consists of constant vectors,
so it is singular, as is the radical of every surjective polar quotient.
This preserves the central radical in the normal row of 14.2.16/F.1.12.
-/

public section
namespace UniformBinaryPolar
open QuadraticMap
variable {n : ℕ}

private theorem uniform_basis (i j : Fin n) :
    form n (Pi.single i 1) (Pi.single j 1) = if i = j then 0 else 1 := by
  classical
  rw [form_apply_basis]
  by_cases he : i = j
  · subst j
    simp [Pi.single_apply,CharTwo.add_self_eq_zero]
  · simp [Pi.single_apply,he]

private theorem value_basis_sum
    (Q : QuadraticForm (ZMod 2) (V n))
    (hB : Q.polarBilin = form n) (hQ : ∀ i, Q (Pi.single i 1) = 0)
    (s : Finset (Fin n)) :
    Q (∑ i ∈ s, Pi.single i 1) = (s.card.choose 2 : ZMod 2) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,QuadraticMap.map_add Q,hQ,ih,zero_add]
    have hp : polar Q (Pi.single a 1) (∑ i ∈ s,Pi.single i 1) = (s.card : ZMod 2) := by
      rw [←QuadraticMap.polarBilin_apply_apply,hB,map_sum]
      calc
        (∑ i ∈ s,form n (Pi.single a 1) (Pi.single i 1)) = ∑ i ∈ s,(1 : ZMod 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [uniform_basis,if_neg (by rintro rfl; exact ha hi)]
        _ = (s.card : ZMod 2) := by simp
    rw [hp,Finset.card_insert_of_notMem ha,Nat.choose_succ_succ,Nat.choose_one_right,Nat.cast_add]
    exact add_comm _ _

theorem uniform_ones_singular
    (Q : QuadraticForm (ZMod 2) (V n))
    (hB : Q.polarBilin = form n) (hQ : ∀ i, Q (Pi.single i 1) = 0)
    (hn : n = 5 ∨ n = 9) : Q (fun _ => 1) = 0 := by
  have he : (fun _ : Fin n => (1 : ZMod 2)) = ∑ i : Fin n,Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  rw [he,value_basis_sum Q hB hQ]
  simp only [Finset.card_univ,Fintype.card_fin]
  rcases hn with rfl | rfl <;> norm_num [Nat.choose] <;> decide

private theorem radical_constant (x : (form n).ker) (i j : Fin n) : x.val i = x.val j := by
  have h (k : Fin n) : (∑ a, x.val a) + x.val k = 0 := by
    rw [←form_apply_basis]
    exact congrArg (fun f : Module.Dual (ZMod 2) (V n) => f (Pi.single k 1)) x.property
  exact add_left_cancel ((h i).trans (h j).symm)

theorem uniform_radical_singular
    (Q : QuadraticForm (ZMod 2) (V n))
    (hB : Q.polarBilin = form n) (hQ : ∀ i, Q (Pi.single i 1) = 0)
    (hn : n = 5 ∨ n = 9) (x : V n) (hx : x ∈ (form n).ker) : Q x = 0 := by
  have hpos : 0 < n := by rcases hn with rfl | rfl <;> decide
  let j : Fin n := ⟨0,hpos⟩
  have he : x = x j • (fun _ : Fin n => (1 : ZMod 2)) := by
    funext i
    simpa using radical_constant ⟨x,hx⟩ i j
  rw [he,Q.map_smul,uniform_ones_singular Q hB hQ hn]
  simp

/-- A quotient of the uniform five- or nine-point quadratic space has
singular radical, retaining a possible one-dimensional radical. -/
theorem radical_singular_of_uniform_pullback
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hp : Q.polarBilin.compl₁₂ f f = form n)
    (hQ : ∀ i, Q (f (Pi.single i 1)) = 0)
    (hn : n = 5 ∨ n = 9) (x : W) (hx : x ∈ Q.polarBilin.ker) : Q x = 0 := by
  obtain ⟨y,rfl⟩ := hf x
  have hB : (Q.comp f).polarBilin = form n := by
    rw [QuadraticMap.polarBilin_comp]
    exact hp
  have hy : y ∈ (form n).ker := by
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    have hz := congrArg (fun B : LinearMap.BilinForm (ZMod 2) (V n) => B y z) hp
    have hxz := congrArg (fun l => l (f z)) hx
    exact hz.symm.trans hxz
  exact uniform_radical_singular (Q.comp f) hB hQ hn y hy
end UniformBinaryPolar
