module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedRootGeometry.PermutationGeometry.Candidates
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.FinCases

/-!
# Cycle type and generation at a normalized marked pivot

The complementary Klein four supplies three disjoint transpositions after
multiplication by (01). For its first nonidentity element, the centralizer
of (01)(23)(45) contains (04)(15). Conjugating (25) by this element gives
(12). The two centralizers therefore contain all adjacent transpositions.
Conjugation by permutations fixing (01) treats the other two choices.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), proof of Lemma 4.8, p.41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange.PivotPermutations

open Equiv Equiv.Perm Subgroup

private theorem generation : centralizer ({base} : Set P) ⊔ centralizer ({base * klein0} : Set P) = ⊤ := by
  let H := centralizer ({base} : Set P) ⊔ centralizer ({base * klein0} : Set P)
  have first {x : P} (hx : x * base = base * x) : x ∈ H :=
    mem_sup_left (mem_centralizer_singleton_iff.mpr hx)
  have second {x : P} (hx : x * (base * klein0) = (base * klein0) * x) : x ∈ H :=
    mem_sup_right (mem_centralizer_singleton_iff.mpr hx)
  let w : P := swap 0 4 * swap 1 5
  have hw : w ∈ H := second (by decide +kernel)
  have h25 : (swap 2 5 : P) ∈ H := first (by decide +kernel)
  have h12 : (swap 1 2 : P) ∈ H := by
    have he : w * swap 2 5 * w⁻¹ = (swap 1 2 : P) := by decide +kernel
    rw [← he]
    exact H.mul_mem (H.mul_mem hw h25) (H.inv_mem hw)
  have hadj (i : Fin 5) : (swap i.castSucc i.succ : P) ∈ H := by
    fin_cases i
    · exact first (by decide +kernel)
    · exact h12
    · exact first (by decide +kernel)
    · exact first (by decide +kernel)
    · exact first (by decide +kernel)
  apply top_unique
  rw [← closure_eq_top_of_mclosure_eq_top (mclosure_swap_castSucc_succ 5)]
  exact (closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hadj i)

private theorem map_centralizer_equiv {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (x : G) :
    (centralizer ({x} : Set G)).map e.toMonoidHom = centralizer ({e x} : Set K) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hy
  · intro hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hy

/-- Transport generation by two literal element centralizers through an isomorphism. -/
public theorem generation_transport {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (x y : G)
    (h : centralizer ({e x} : Set K) ⊔ centralizer ({e y} : Set K) = ⊤) :
    centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, map_centralizer_equiv, map_centralizer_equiv, h]
  simp

private theorem normalized_cases {q : P} (hc : q = klein0 ∨ q = klein1 ∨ q = klein2) :
    (base * q).cycleType = {2, 2, 2} ∧
      centralizer ({base} : Set P) ⊔ centralizer ({base * q} : Set P) = ⊤ := by
  have basic : (base * klein0).cycleType = {2, 2, 2} := by decide +kernel
  have transport (g : P) (hg : g * base * g⁻¹ = base) (hq : g * q * g⁻¹ = klein0) :
      (base * q).cycleType = {2, 2, 2} ∧
        centralizer ({base} : Set P) ⊔ centralizer ({base * q} : Set P) = ⊤ := by
    let e : P ≃* P := MulAut.conj g
    have hez : e base = base := hg
    have heq : e q = klein0 := hq
    have het : e (base * q) = base * klein0 := by rw [map_mul, hez, heq]
    constructor
    · rw [← het] at basic
      exact (cycleType_conj (σ := base * q) (τ := g)).symm.trans basic
    · exact generation_transport e base (base * q) (by rw [hez, het]; exact generation)
  rcases hc with rfl | rfl | rfl
  · exact ⟨basic, generation⟩
  · exact transport (swap 3 4) (by decide +kernel) (by decide +kernel)
  · exact transport (swap 3 5) (by decide +kernel) (by decide +kernel)

/-- The literal two centralizers generate, and the pivot has triple cycle
type, whenever the even involution belongs to an abelian subgroup normalized
by the marked transposition centralizer. -/
public theorem normalized (q : P) (hq2 : q * q = 1) (hqbase : q * base = base * q)
    (hq1 : q ≠ 1) (hqsign : sign q = 1)
    (hconj : ∀ g : P, g * base = base * g → commutesConjugate q g) :
    (base * q).cycleType = {2, 2, 2} ∧
      centralizer ({base} : Set P) ⊔ centralizer ({base * q} : Set P) = ⊤ := by
  apply normalized_cases
  exact candidates q ⟨hq2, hqbase, hq1, hqsign,
    hconj (swap 2 3) (by decide +kernel),
    hconj (swap 3 4) (by decide +kernel),
    hconj (swap 4 5) (by decide +kernel)⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange.PivotPermutations
