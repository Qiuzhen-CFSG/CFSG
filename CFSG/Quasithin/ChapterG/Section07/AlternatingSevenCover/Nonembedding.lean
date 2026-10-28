module

public import Theory.Alternating.theorem_5_2_3
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.ExtendScalars
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The triple cover of A₇ has no faithful action of degree three

The inverse image of a cyclic subgroup of order five is abelian of order
fifteen. A normalizer element induces squaring on that cyclic quotient, an
automorphism of order four. Over an algebraic closure the automizer acts
faithfully on the distinct weights, so three-dimensional faithfulness would
embed it in S₃. Taking sixth powers gives a contradiction.

This proves in particular the nonembedding in SL₃(4) used in
Aschbacher–Smith, G.7.3, printed p.349 (PDF p.360).
-/

public section

open Subgroup
open scoped TensorProduct

namespace CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover

set_option maxRecDepth 10000

private def a : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4,
    by change Equiv.Perm.sign _ = 1; simp [map_mul]⟩

private def b : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 5 6,
    by change Equiv.Perm.sign _ = 1; simp [map_mul]⟩

private theorem a_order : orderOf a = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime (p := 5) <;> decide

private theorem square_zpowers {G : Type*} [Group G] (x : G) (hpow : (x ^ 2) ^ 3 = x) :
    zpowers (x ^ 2) = zpowers x := by
  apply le_antisymm (zpowers_le.mpr ((zpowers x).pow_mem (mem_zpowers x) 2))
  apply zpowers_le.mpr
  have h := (zpowers (x ^ 2)).pow_mem (mem_zpowers (x ^ 2)) 3
  rwa [hpow] at h

private theorem b_normalizes : b ∈ normalizer (zpowers a : Set (alternatingGroup (Fin 7))) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (b * a * b⁻¹) = zpowers a
  have hconj : b * a * b⁻¹ = a ^ 2 := by decide
  rw [hconj]
  exact square_zpowers a (by decide)

private theorem b_six_not_centralizes : b ^ 6 * a * (b ^ 6)⁻¹ ≠ a := by decide

theorem degree_gt_three {L : Type*} [Group L] [Finite L]
    (q : L →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker ≤ center L) (hc : Nat.card q.ker = 3)
    {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (rho : Representation F L V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V ≤ 3) : False := by
  let Q := (zpowers a).comap q
  let p : Q →* zpowers a := q.subgroupComap (zpowers a)
  have hpker : p.ker ≤ center Q := by
    intro x hx
    have hxq : q x = 1 := congrArg Subtype.val hx
    have hxz := hk hxq
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hxz y)
  let : IsMulCommutative Q := p.isMulCommutative_of_isCyclic_of_ker_le_center hpker
  have hQc : Nat.card Q = 15 := by
    rw [GLS3.Chapter5.SchurPresentation.card_comap_mul q hq (zpowers a),
      Nat.card_zpowers, a_order, hc]
  let E := AlgebraicClosure F
  let tau := rho.extendScalars E
  have hfaith : Function.Injective tau := (Representation.extendScalars_faithful_iff E rho).mp hrho
  have horder : (Nat.card Q : E) ≠ 0 := by
    rw [hQc]
    exact (CharP.cast_eq_zero_iff E 2 15).not.mpr (by decide)
  have hdim' : Module.finrank E (E ⊗[F] V) ≤ 3 := by
    simpa only [Module.finrank_baseChange] using hdim
  obtain ⟨j, hj⟩ := Representation.automizer_embeds_perm_of_abelian tau Q hfaith horder 3 hdim'
  obtain ⟨g, hg⟩ := hq b
  have hgN : g ∈ normalizer (Q : Set L) :=
    (zpowers a).le_normalizer_comap q (by simpa only [mem_comap, hg] using b_normalizes)
  let n : normalizer (Q : Set L) := ⟨g, hgN⟩
  let alpha : Q.normalizerMonoidHom.range := ⟨Q.normalizerMonoidHom n, n, rfl⟩
  have hjpow : j alpha ^ 6 = 1 := by
    simpa only [Nat.card_perm, Nat.card_fin, show Nat.factorial 3 = 6 by norm_num]
      using pow_card_eq_one' (x := j alpha)
  have hapow : alpha ^ 6 = 1 := hj (by simpa using hjpow)
  have hn6 : Q.normalizerMonoidHom (n ^ 6) = 1 := by
    have h : (Q.normalizerMonoidHom n) ^ 6 = 1 := congrArg Subtype.val hapow
    rwa [map_pow]
  obtain ⟨x, hx⟩ := hq a
  have hxQ : x ∈ Q := by simpa only [Q, mem_comap, hx] using mem_zpowers a
  have hconj := congrArg (fun f : MulAut Q => f ⟨x, hxQ⟩) hn6
  have hconj' : g ^ 6 * x * (g ^ 6)⁻¹ = x := congrArg Subtype.val hconj
  have h := congrArg q hconj'
  rw [map_mul, map_mul, map_inv, map_pow, hg, hx] at h
  exact b_six_not_centralizes h

theorem not_embeds_sl3 {L : Type*} [Group L] [Finite L]
    (q : L →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker ≤ center L) (hc : Nat.card q.ker = 3)
    {F : Type*} [Field F] [CharP F 2]
    (j : L →* Matrix.SpecialLinearGroup (Fin 3) F) : ¬ Function.Injective j := by
  intro hj
  let rho := (Representation.generalLinearNatural (F := F) 3).comp
    (Matrix.SpecialLinearGroup.toGL.comp j)
  have hrho : Function.Injective rho :=
    (Representation.generalLinearNatural_injective 3).comp
      (Matrix.SpecialLinearGroup.toGL_injective.comp hj)
  exact degree_gt_three q hq hk hc rho hrho (by simp)

end CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover
