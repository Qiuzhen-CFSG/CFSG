module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The unique outer involution and its exact inner-twist equation

Traces of products of two root matrices range over the coefficient field.
Trace invariance therefore proves that an entrywise field automorphism is
inner only when it is trivial. The exceptional graph map's n-th power is a
noninner involution for |F| = 2^n, n > 1: for even n it is the half-power
of Frobenius, and for odd n it interchanges the two parabolic types.

Under the explicit diagram-preserving semilinear coverage premise, the
outer quotient is cyclic. It has at most two square roots of one, so every
involutory automorphism is either induced by an actual matrix involution
or is an inner twist of that specified graph power. The latter matrix
satisfies the exact cocycle equation. Eliminating its twist remains a
separate descent problem; outer-coset membership does not prove conjugacy.

Source: Aschbacher–Smith, Notation 16.1.3 and Lemma 16.1.4, printed
pp.1170–1173 of `refs/quasithin.pdf`; GLS3, Theorem 2.5.12(e).
-/

@[expose] public section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open Representation.OneCohomology.SymplecticFour Matrix
variable {F : Type*} [Field F] [CharP F 2]

private def traceElement (t : F) : Sp F := rootElement 0 t * rootElement 1 1

private theorem trace_traceElement (t : F) : Matrix.trace (traceElement t).val = t := by
  simp [traceElement, rootElement, rootMatrix, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
    Matrix.one_apply, CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm]

/-- No nontrivial entrywise field automorphism is inner. -/
theorem field_eq_one_of_inner (σ : F ≃+* F)
    (hi : fieldAutomorphism σ ∈ MulAut.innerSubgroup (Sp F)) : σ = 1 := by
  obtain ⟨g, hg⟩ := hi
  apply RingEquiv.ext
  intro t
  have he := congrArg (fun a : MulAut (Sp F) => Matrix.trace (a (traceElement t)).val) hg
  have hc : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  change Matrix.trace (g.val * (traceElement t).val * (g⁻¹).val) =
    Matrix.trace ((traceElement t).val.map σ) at he
  rw [Matrix.trace_mul_cycle, hc, Matrix.one_mul, ← AddMonoidHom.map_trace,
    trace_traceElement] at he
  exact he.symm

/-- Field automorphisms inject into the actual outer quotient. -/
theorem outerFieldHom_injective : Function.Injective (outerFieldHom (F := F)) := by
  apply (outerFieldHom (F := F)).ker_eq_bot_iff.mp
  apply bot_unique
  intro σ hσ
  exact field_eq_one_of_inner σ ((QuotientGroup.eq_one_iff _).mp hσ)

variable [Finite F]

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private noncomputable def forgetFieldAlgebra : (F ≃ₐ[ZMod 2] F) →* (F ≃+* F) := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact { toFun := AlgEquiv.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }

private theorem forgetFieldAlgebra_frobenius :
    forgetFieldAlgebra (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) =
      frobeniusEquiv F 2 := by
  apply RingEquiv.ext
  intro t
  change t ^ Fintype.card (ZMod 2) = t ^ 2
  rw [ZMod.card]

/-- The coefficient Frobenius has the exact extension degree as its order. -/
theorem frobenius_order {n : ℕ} (hcard : Nat.card F = 2^n) :
    orderOf (frobeniusEquiv F 2) = n := by
  have hf : Function.Injective (forgetFieldAlgebra (F := F)) := by
    intro a b h
    apply AlgEquiv.ext
    intro t
    exact DFunLike.congr_fun h t
  have hdim : Module.finrank (ZMod 2) F = n := by
    let := Fintype.ofFinite F
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod, hcard] using hc.symm
  rw [← forgetFieldAlgebra_frobenius, orderOf_injective _ hf,
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hdim]

open ExceptionalGraph

/-- For even degree, the exceptional half-order power is exactly a field map. -/
theorem graph_pow_eq_field_of_even {n : ℕ} (hn : Even n) :
    graphAut (F := F) ^ n = fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) := by
  conv_lhs => rw [← Nat.two_mul_div_two_of_even hn, pow_mul, graphAut_square]
  exact (fieldAutomorphismHom.map_pow _ _).symm

theorem graph_pow_square {n : ℕ} (hcard : Nat.card F = 2^n) :
    (graphAut (F := F) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, graphAut_square]
  change fieldAutomorphismHom (frobeniusEquiv F 2) ^ n = 1
  rw [← map_pow, ← frobenius_order hcard, pow_orderOf_eq_one, map_one]

/-- The prescribed representative survives in the outer quotient. -/
theorem graph_pow_not_inner {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1 < n) :
    graphAut (F := F) ^ n ∉ MulAut.innerSubgroup (Sp F) := by
  intro hi
  rcases Nat.even_or_odd n with he | ho
  · rw [graph_pow_eq_field_of_even he] at hi
    have horder : orderOf (frobeniusEquiv F 2 ^ (n / 2)) = 2 := by
      rw [← frobenius_order hcard]
      apply orderOf_pow_orderOf_div
      · rw [frobenius_order hcard]
        omega
      · rw [frobenius_order hcard]
        exact even_iff_two_dvd.mp he
    rw [field_eq_one_of_inner _ hi, orderOf_one] at horder
    contradiction
  · have hF : 2 < Nat.card F := by
      rw [hcard]
      exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
    let ρ := parabolicClassAction hF
    have hsq : ρ (graphAut (F := F)) ^ 2 = 1 := by
      rw [← map_pow, graphAut_square]
      exact (mem_parabolicClassAction_ker_iff hF _).mpr (field_preservesDiagram _)
    have hpow : ρ (graphAut (F := F)) ^ n = ρ graphAut := by
      obtain ⟨k, hk⟩ := ho
      rw [hk, pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
    have heq : ρ (graphAut (F := F)) = 1 := by
      rw [← hpow, ← map_pow]
      obtain ⟨g, hg⟩ := hi
      rw [← hg]
      exact (mem_parabolicClassAction_ker_iff hF _).mpr (inner_preservesDiagram g)
    exact graphAut_not_preservesDiagram ((mem_parabolicClassAction_ker_iff hF _).mp heq)

private theorem cyclic_square_eq_one_or {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (s : G) (hs : s ^ 2 = 1) (hne : s ≠ 1) (a : G) (ha : a ^ 2 = 1) :
    a = 1 ∨ a = s := by
  classical
  let := Fintype.ofFinite G
  by_contra! h
  have hl : ({1, s, a} : Finset G) ⊆ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [hs, ha]
  have hc := (Finset.card_le_card hl).trans (IsCyclic.card_pow_eq_one_le (by decide : 0 < 2))
  simp [Finset.card_insert_of_notMem, Ne.symm hne,
    Ne.symm h.1, Ne.symm h.2] at hc


/-- Exhaustive reduction to a genuine inner involution or an explicit cocycle twist. -/
theorem involution_inner_or_twist {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (a : MulAut (Sp F)) (ha : orderOf a = 2) :
    (∃ g : Sp F, orderOf g = 2 ∧ a = MulAut.conj g) ∨
      (∃ g : Sp F, a = MulAut.conj g * graphAut ^ n ∧ g * (graphAut ^ n) g = 1) := by
  let π : MulAut (Sp F) →* MulAut.Outer (Sp F) := QuotientGroup.mk' _
  let : IsCyclic (MulAut.Outer (Sp F)) := outer_isCyclic_of_card hcard hn hclass
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hp : (π a) ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have hs : (π (graphAut (F := F) ^ n)) ^ 2 = 1 := by
    rw [← map_pow, graph_pow_square hcard, map_one]
  have hne : π (graphAut (F := F) ^ n) ≠ 1 := by
    intro h
    exact graph_pow_not_inner hcard hn ((QuotientGroup.eq_one_iff _).mp h)
  rcases cyclic_square_eq_one_or _ hs hne _ hp with hi | ht
  · exact Or.inl (inner_involution a ha ((QuotientGroup.eq_one_iff _).mp hi))
  · have hm : a / graphAut ^ n ∈ MulAut.innerSubgroup (Sp F) :=
      QuotientGroup.eq_iff_div_mem.mp ht
    obtain ⟨g, hg⟩ := hm
    have he : a = MulAut.conj g * graphAut ^ n := (eq_div_iff_mul_eq'.mp hg).symm
    refine Or.inr ⟨g, he, ?_⟩
    apply (inner_twist_square_eq_one_iff _ (graph_pow_square hcard) g).mp
    rw [← he]
    exact ha2

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
