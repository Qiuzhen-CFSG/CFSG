module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.OrbitDefect.OrbitProfile
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Representatives

/-!
# The exceptional normal form for the orbit pattern 4+2+2

An elementary abelian subgroup of `Sym(8)` with three orbits, each of size two
or four, has one four-point orbit and two pairs. Choose arbitrary bijections
from the standard blocks to these orbits to obtain an actual labeling
permutation. On any orbit, an element of an abelian group fixing one point
fixes every point. Consequently the involutions on the four-point block are
identity or double transpositions, giving the regular Klein four group under
any labeling. The pair actions give the other two standard generators.

A kernel-checked calculation on the three block permutation groups identifies
each conjugated element with one of the sixteen concrete exceptional words.
Containment and the assumed order sixteen then give equality. In particular,
the independent-evaluation premise supplied by the orbit-profile theorem is
not needed separately.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2(5), printed pp. 83–84.
-/

public section

open scoped BigOperators IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

private def block (x : Fin 8) : Fin 3 := if x < 4 then 0 else if x < 6 then 1 else 2

private theorem block_card (i : Fin 3) :
    Nat.card {x : Fin 8 // block x = i} = if i = 0 then 4 else 2 := by
  fin_cases i <;> simp only [Nat.card_eq_fintype_card] <;> decide

private theorem enumerate_sizes {Q : Type} [Fintype Q] (s : Q → ℕ)
    (hc : Nat.card Q = 3) (hs : ∀ q, s q = 2 ∨ s q = 4)
    (ht : ∑ q, s q = 8) :
    ∃ e : Fin 3 ≃ Q, ∀ i, s (e i) = if i = 0 then 4 else 2 := by
  classical
  let e := (Fintype.equivFinOfCardEq (by simpa [Nat.card_eq_fintype_card] using hc)).symm
  have ht' : s (e 0) + s (e 1) + s (e 2) = 8 := by
    have h := (e.sum_comp s).trans ht
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using h
  have h0 := hs (e 0)
  have h1 := hs (e 1)
  have h2 := hs (e 2)
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · refine ⟨(Equiv.swap 0 2).trans e, ?_⟩
      intro i
      fin_cases i <;> simp [Equiv.swap_apply_def, h0, h1, show s (e 2) = 4 by omega]
    · refine ⟨(Equiv.swap 0 1).trans e, ?_⟩
      intro i
      fin_cases i <;> simp [Equiv.swap_apply_def, h0, h1, show s (e 2) = 2 by omega]
  · refine ⟨e, ?_⟩
    intro i
    fin_cases i <;> simp [h0, show s (e 1) = 2 by omega, show s (e 2) = 2 by omega]

private theorem orbit_label (A : Subgroup (Equiv.Perm (Fin 8)))
    (hs : ∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2 ∨
      Nat.card (MulAction.orbit A x) = 4)
    (hc : Nat.card (MulAction.orbitRel.Quotient A (Fin 8)) = 3) :
    ∃ g : Equiv.Perm (Fin 8), ∀ i j,
      g j ∈ MulAction.orbit A (g i) ↔ block j = block i := by
  classical
  let Q := MulAction.orbitRel.Quotient A (Fin 8)
  let : Fintype Q := Fintype.ofFinite Q
  have hs' (q : Q) : Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4 := by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact hs q.out
  have ht : ∑ q : Q, Nat.card q.orbit = 8 := by
    simpa only [Nat.card_sigma, Nat.card_fin] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' A (Fin 8))).symm
  obtain ⟨e, he⟩ := enumerate_sizes (fun q : Q => Nat.card q.orbit) hc hs' ht
  let f (i : Fin 3) : {x : Fin 8 // block x = i} ≃ (e i).orbit :=
    Fintype.equivOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using
      ((block_card i).trans (he i).symm))
  let g : Equiv.Perm (Fin 8) := (Equiv.sigmaFiberEquiv block).symm |>.trans
    (Equiv.sigmaCongr e f) |>.trans (MulAction.selfEquivSigmaOrbits' A (Fin 8)).symm
  have hg (i : Fin 8) : Quotient.mk'' (g i) = e (block i) := by
    exact MulAction.orbitRel.Quotient.mem_orbit.mp (f (block i) ⟨i, rfl⟩).property
  refine ⟨g, fun i j => ?_⟩
  change MulAction.orbitRel A (Fin 8) (g j) (g i) ↔ _
  rw [← Quotient.eq'', hg, hg]
  exact e.injective.eq_iff

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The local permutation calculation on blocks of sizes four, two, and two. -/
private theorem block_permutation_words : ∀ f : (i : Fin 3) → Equiv.Perm {x : Fin 8 // block x = i},
    (∀ x, f 0 (f 0 x) = x) →
    (∀ x y, f 0 x = x → f 0 y = y) →
    ∃ k : Fin 16, ∀ i x, Eight.exceptionalWords k x.val = (f i x).val := by
  decide +kernel

private theorem mem_exceptional_of_blocks (p : Equiv.Perm (Fin 8))
    (hb : ∀ x, block (p x) = block x)
    (hp : ∀ x, p (p x) = x)
    (hf : ∀ x y, block x = 0 → block y = 0 → p x = x → p y = y) :
    p ∈ exceptional 8 (by decide) := by
  let f (i : Fin 3) := p.subtypePerm (p := fun x => block x = i)
    (fun x => by rw [hb x])
  obtain ⟨k, hk⟩ := block_permutation_words f
    (fun x => Subtype.ext (hp x.val))
    (fun x y h => Subtype.ext (hf x.val y.val x.property y.property
      (congrArg Subtype.val h)))
  apply (Eight.mem_exceptional_iff p).mpr
  exact ⟨k, Equiv.ext (fun x => hk (block x) ⟨x, rfl⟩)⟩

private theorem fixes_orbit (A : Subgroup (Equiv.Perm (Fin 8)))
    [IsMulCommutative A] (a : A) {x y : Fin 8}
    (hx : a.val x = x) (hy : y ∈ MulAction.orbit A x) : a.val y = y := by
  obtain ⟨b, rfl⟩ := hy
  change a.val (b.val x) = b.val x
  calc
    a.val (b.val x) = b.val (a.val x) :=
      congrArg (fun c : A => c.val x) (mul_comm a b)
    _ = b.val x := congrArg b.val hx

/-- An elementary abelian degree-eight action with three orbits of sizes two
or four and order sixteen is conjugate to the concrete exceptional subgroup. -/
theorem isConjugateTo_exceptional_of_three_orbits
    (A : Subgroup (Equiv.Perm (Fin 8))) (hA : IsElementaryTwo A)
    (hs : ∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2 ∨
      Nat.card (MulAction.orbit A x) = 4)
    (hc : Nat.card (MulAction.orbitRel.Quotient A (Fin 8)) = 3)
    (hcard : Nat.card A = 16) : IsConjugateTo A (exceptional 8 (by decide)) := by
  classical
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨g, hg⟩ := orbit_label A hs hc
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro a ha
    let p : Equiv.Perm (Fin 8) := (MulAut.conj g⁻¹) a
    have hgp (x : Fin 8) : g (p x) = a (g x) := by
      simp [p, MulAut.conj_apply]
    have hp2 : p ^ 2 = 1 := by
      dsimp only [p]
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian a ha, map_one]
    refine ⟨p, mem_exceptional_of_blocks p ?_ ?_ ?_, ?_⟩
    · intro x
      apply (hg x (p x)).mp
      rw [hgp]
      exact MulAction.mem_orbit (g x) (⟨a, ha⟩ : A)
    · intro x
      exact congrArg (fun q : Equiv.Perm (Fin 8) => q x) hp2
    · intro x y hx hy hfix
      apply g.injective
      rw [hgp]
      apply fixes_orbit A ⟨a, ha⟩ (x := g x)
      · simpa only [hgp] using congrArg g hfix
      · exact (hg x y).mpr (hy.trans hx.symm)
    · simp [p, MulAut.conj_apply, mul_assoc]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Eight.card_exceptional, hcard]

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
