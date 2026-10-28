module

public import CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Elimination of the global alternatives in 12.2.13

The block parameter is determined by the order of the actual quotient
L/O₂(L). The natural marking and the block marking both identify that same
quotient; the orders of GL₃(2), GL₄(2), GL₅(2) distinguish the parameters.
Only after this alignment do we use the n-specific exclusion of L_(n+1)(2).
The A₉ and M₂₄ alternatives are separately excluded as in 12.8.1(1).

The remaining point-centralizer escape is transported to every nonzero
vector using the actual L-action. Its application to a marked flag gives
12.8.3(4) and the SourceGeometry conclusion G₁ ∈ H_z.
Source: Aschbacher–Smith, Theorem 12.2.13 and Lemma 12.8.3(4), pp.799,849–850.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08
open Section02 InvariantFlag BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem linear_card (d : ℕ) :
    Nat.card (LinearGroup d) = ∏ i : Fin d, (2 ^ d - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear d).toEquiv, Matrix.card_GL_field]
  simp

namespace HigherRankHypothesis
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
variable (h : HigherRankHypothesis K T L V n)
include h

/-- Both natural markings identify the same original two-core quotient. -/
theorem block_parameter {d : ℕ} (hd : d = 3 ∨ d = 4)
    (hblock : ChapterC.IsLinearTwoBlock L d) : d = n := by
  let := h.chosen.elementary
  obtain ⟨e⟩ := hblock.2.2.2.quotient_iso
  have hc := Nat.card_congr
    ((h.naturalMarking.quotientEquiv.symm.trans e).trans (slEquivLinear d)).toEquiv
  rw [linear_card, linear_card] at hc
  obtain ⟨hnlo, hnhi⟩ := h.rank
  interval_cases n <;> rcases hd with rfl | rfl <;>
    first | rfl | (exfalso; norm_num [Fin.prod_univ_succ] at hc)

/-- Apply the FULL universal earlier theorem and eliminate its three actual
global alternatives. No escape premise for this setup is assumed. -/
theorem exists_escaping_vector (earlier : Theorem12213 K) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  rcases earlier G T L V h.source h.chosen with hv | hl | ha | hm
  · exact hv
  · obtain ⟨d, hd, hb, hg⟩ := hl
    have he := h.block_parameter hd hb
    subst d
    exact (h.no_nextLinear hg).elim
  · exact (h.no_A9 ha.2).elim
  · exact (h.no_M24 hm.2).elim

/-- The original L action is transitive on the nonidentity vectors. -/
theorem vector_transitive {x y : G} (hx : x ∈ V) (hy : y ∈ V)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, l * x * l⁻¹ = y := by
  let := h.chosen.elementary
  let x' : Additive V := Additive.ofMul ⟨x, hx⟩
  let y' : Additive V := Additive.ofMul ⟨y, hy⟩
  have hx0 : x' ≠ 0 := fun he => hx1 (congrArg (fun v : Additive V => (v.toMul : G)) he)
  have hy0 : y' ≠ 0 := fun he => hy1 (congrArg (fun v : Additive V => (v.toMul : G)) he)
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive V) x' hx0
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive V) y' hy0
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  have he : a x' = y' := by
    have he := ha (ex 1)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at he
    simpa [ex, ey] using he.symm
  obtain ⟨l, hl⟩ := h.naturalMarking.geometryAction.surjective a
  refine ⟨l, l.property, ?_⟩
  have hc := h.naturalMarking.geometryAction.conjugation l x'
  rw [hl, he] at hc
  exact hc.symm

/-- Escape holds at every nonidentity element of the chosen V. -/
theorem vector_centralizer_escape (earlier : Theorem12213 K)
    {x : G} (hx : x ∈ V) (hx1 : x ≠ 1) :
    ¬ centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v, hv, hv1, hescape⟩ := h.exists_escaping_vector earlier
  obtain ⟨l, hl, he⟩ := h.vector_transitive hx hv hx1 hv1
  intro hc
  apply hescape
  intro y hy
  have hyc : l⁻¹ * y * l ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hyv := mem_centralizer_singleton_iff.mp hy
    rw [← he] at hyv
    have hh := congrArg (fun a : G => l⁻¹ * a * l) hyv
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel,
      mul_one] using hh
  have hlM := L.le_normalizer hl
  have hyM := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem hlM (hc hyc))
    ((normalizer (L : Set G)).inv_mem hlM)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel,
    mul_one] using hyM

/-- Actual application to the marked source point normalizer. -/
theorem flag_escape (F : InvariantFlag T V n) (earlier : Theorem12213 K) :
    ¬ F.H ≤ normalizer (L : Set G) := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by have := h.rank; omega)
  have hne : F.Vi 1 ≠ ⊥ := by intro he; simp [he] at hc
  obtain ⟨x', hx'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let x : G := x'
  have hx : x ∈ F.Vi 1 := x'.property
  have hx1 : x ≠ 1 := fun he => hx' (Subtype.ext he)
  intro hH
  apply h.vector_centralizer_escape earlier (F.le_seed 1 hx) hx1
  have hpoint : F.Vi 1 = zpowers x := by
    have hxe : (⟨x, hx⟩ : F.Vi 1) ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
    have hg := zpowers_eq_top_of_prime_card hc hxe
    have hm := congrArg (map (F.Vi 1).subtype) hg
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      range_subtype, Subgroup.coe_subtype] using hm.symm
  rw [← F.H_eq_centralizer (by have := h.rank; omega) x hpoint]
  exact hH

/-- The existing SourceGeometry consumer now has its escape premise discharged. -/
theorem point_mem_Hz (F : InvariantFlag T V n) (earlier : Theorem12213 K) :
    F.H ∈ F.Hz L (normalizer (L : Set G)) :=
  F.H_mem_Hz (by have := h.rank; omega) L _ (h.flag_escape F earlier)

end HigherRankHypothesis
end CFSG.Quasithin.Chapter12.Section08
