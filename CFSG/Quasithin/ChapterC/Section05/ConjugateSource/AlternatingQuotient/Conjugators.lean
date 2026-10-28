module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.PairAction
public import Mathlib.GroupTheory.GroupAction.Period

/-!
# The original even-order conjugator and its replacements

The actual Frattini stabilizer acts on the proved core pair. The original
x exchanges it and hence has even order. Every other element outside the
core stabilizer also moves U noncentrally: it sends D into the other core,
so centralizing U would force it to fix Q=UD.

Source: Aschbacher–Smith C.5.6(5)–(6), printed pp.157–158.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
open RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- The original conjugator exchanges the two cores, without Φ(D)=1. -/
theorem conjugate_core_swap (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = Q R K := by
  let e := MulAut.conj x⁻¹
  have hiR := (normalizer (R : Set G)).inv_mem hx
  have hiP : x⁻¹ ∈ normalizer (Phi R K : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (h.frattini_invariant x hx hnc)
  have hh := core_pair_preserved h hsource x hx hnc (x⁻¹ * x⁻¹)
    ((normalizer (R : Set G)).mul_mem hiR hiR) ((normalizer (Phi R K : Set G)).mul_mem hiP hiP)
  have he : (MulAut.conj (x⁻¹ * x⁻¹)).toMonoidHom = e.toMonoidHom.comp e.toMonoidHom := by
    ext a
    simp [e, mul_assoc]
  rw [he, ← map_map] at hh
  rcases hh with hh | hh
  · exact hh
  · have hQ := map_injective e.injective hh
    exact (hnc (((map_mono (f := e.toMonoidHom)
      (show U K ≤ Q R K from le_sup_left.trans_eq h.product.symm)).trans_eq hQ).trans
        (h.core.le.trans inf_le_right))).elim

/-- C.5.6(5): the original x has even order, retaining the source Frattini layer. -/
theorem even_order (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    Even (orderOf x) := by
  let e := MulAut.conj x⁻¹
  have hfix : e ^ 2 • Q R K = Q R K := by
    rw [pow_two, mul_smul]
    exact conjugate_core_swap h hsource x hx hnc
  have hd := MulAction.pow_smul_eq_iff_period_dvd.mp hfix
  have hn : MulAction.period e (Q R K) ≠ 1 := by
    intro he
    have hm := MulAction.period_eq_one_iff.mp he
    have hQ : (Q R K).map e.toMonoidHom = Q R K := hm
    exact hnc (((map_mono (f := e.toMonoidHom)
      (show U K ≤ Q R K from le_sup_left.trans_eq h.product.symm)).trans_eq hQ).trans
        (h.core.le.trans inf_le_right))
  have hp : MulAction.period e (Q R K) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  apply even_iff_two_dvd.mpr
  have he := (hp ▸ MulAction.period_dvd_orderOf e (Q R K)).trans
    (orderOf_map_dvd MulAut.conj x⁻¹)
  simpa only [orderOf_inv] using he

/-- Every element of N_R(Φ(D))'s ambient stabilizer outside N(Q) supplies
another genuinely noncommuting conjugate of the original module. -/
theorem noncentral_of_core_moved (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (y : G) (hy : y ∈ normalizer (R : Set G)) (hyP : y ∈ normalizer (Phi R K : Set G))
    (hyQ : y ∉ normalizer (Q R K : Set G)) :
    ¬ (U K).map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer (U K : Set G) := by
  let e := MulAut.conj y⁻¹
  let e₀ := MulAut.conj x⁻¹
  have hiR := (normalizer (R : Set G)).inv_mem hx
  have hiP : x⁻¹ ∈ normalizer (Phi R K : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (h.frattini_invariant x hx hnc)
  have hyiR := (normalizer (R : Set G)).inv_mem hy
  have hyiP := (normalizer (Phi R K : Set G)).inv_mem hyP
  have hmove : (Q R K).map e.toMonoidHom ≠ Q R K := by
    intro he
    have hi : y⁻¹ ∈ normalizer (Q R K : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
    exact hyQ (by simpa only [inv_inv] using (normalizer (Q R K : Set G)).inv_mem hi)
  have hswap := (core_pair_preserved h hsource x hx hnc y⁻¹ hyiR hyiP).resolve_left hmove
  have hother : ((Q R K).map e₀.toMonoidHom).map e.toMonoidHom = Q R K := by
    have hh := core_pair_preserved h hsource x hx hnc (y⁻¹ * x⁻¹)
      ((normalizer (R : Set G)).mul_mem hyiR hiR) ((normalizer (Phi R K : Set G)).mul_mem hyiP hiP)
    have he : (MulAut.conj (y⁻¹ * x⁻¹)).toMonoidHom = e.toMonoidHom.comp e₀.toMonoidHom := by
      ext a
      simp [e, e₀, mul_assoc]
    rw [he, ← map_map] at hh
    rcases hh with hh | hh
    · exact hh
    · have hQ := map_injective e.injective (hh.trans hswap.symm)
      exact (hnc (((map_mono (f := e₀.toMonoidHom)
        (show U K ≤ Q R K from le_sup_left.trans_eq h.product.symm)).trans_eq hQ).trans
          (h.core.le.trans inf_le_right))).elim
  have hD : (D R K).map e.toMonoidHom ≤ Q R K := by
    have hd : D R K ≤ (Q R K).map e₀.toMonoidHom :=
      le_sup_right.trans_eq (h.opposite_eq_conjugate x hx hnc)
    exact (map_mono hd).trans_eq hother
  intro hcomm
  have hU : (U K).map e.toMonoidHom ≤ Q R K := by
    have hc : Q R K = S R ⊓ centralizer (U K : Set G) := h.core
    rw [hc]
    exact le_inf ((map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R hyiR))) hcomm
  have hQle : (Q R K).map e.toMonoidHom ≤ Q R K := by
    have hp : Q R K = U K ⊔ D R K := h.product
    conv_lhs => rw [hp, Subgroup.map_sup]
    exact sup_le hU hD
  exact hmove (eq_of_le_of_card_ge hQle (card_map_of_injective e.injective).ge)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
end
