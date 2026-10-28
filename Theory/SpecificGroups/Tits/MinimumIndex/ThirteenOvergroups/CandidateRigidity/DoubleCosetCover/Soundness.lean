module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.Words
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite transition certificates for the two core double-coset covers

A table entry is a literal representative followed by a word in the three
core generators and their inverses. For each entry and each positive standard
generator, a checked transition factors their product as a core word times
another entry. Induction in the finite group's generated submonoid proves
exhaustiveness. No order, distinctness, or GAP coset computation is assumed.

Source: the ATLAS max1 and max2 programs, preserved with attribution in
`MinimumIndex/source/`, and the representative words in `CandidateRigidity.Words`.
-/

namespace Tits.MinimumIndexThirteen.CandidateRigidity.CoreCover
open Theory.GroupTheory Subgroup

/-- The three core generators followed by their inverses. -/
@[expose] public def signedCore (i : Fin 2) : Fin 6 → Atlas1600Group :=
  let c := coreGen (i.castLE (by decide))
  ![c 0, c 1, c 2, (c 0)⁻¹, (c 1)⁻¹, (c 2)⁻¹]

public theorem signedCore_mem (i : Fin 2) (k : Fin 6) :
    signedCore i k ∈ core (i.castLE (by decide)) := by
  have h (j : Fin 3) : coreGen (i.castLE (by decide)) j ∈ core (i.castLE (by decide)) :=
    subset_closure (Set.mem_range_self j)
  fin_cases k
  · exact h 0
  · exact h 1
  · exact h 2
  · exact (core _).inv_mem (h 0)
  · exact (core _).inv_mem (h 1)
  · exact (core _).inv_mem (h 2)

public theorem word_mem (i : Fin 2) (w : List (Fin 6)) :
    evalWord (signedCore i) w ∈ core (i.castLE (by decide)) := by
  induction w with
  | nil => exact (core _).one_mem
  | cons k w ih => exact (core _).mul_mem (signedCore_mem i k) ih

/-- Base-eight digits 1 through 6 encode signed letters; zero ends the word.
The fixed fuel bounds computation, and every decoded result is a core word. -/
@[expose] public def decode : Nat → Nat → List (Fin 6)
  | 0, _ => []
  | n + 1, c => if c = 0 then [] else
      ⟨(c % 8 - 1) % 6, Nat.mod_lt _ (by decide)⟩ :: decode n (c / 8)

@[expose] public def word (c : Nat) : List (Fin 6) := decode 16 c

@[expose] public def repIndex (c : Nat) : Fin 6 :=
  ⟨c % 8 % 6, Nat.mod_lt _ (by decide)⟩

/-- An encoded double-coset representative with an explicit right core factor. -/
@[expose] public def node (i : Fin 2) (c : Nat) : Atlas1600Group :=
  representative i (repIndex c) * evalWord (signedCore i) (word (c / 8))

public theorem node_zero (i : Fin 2) : node i 0 = 1 := by
  change representative i 0 * 1 = 1
  rw [representative_zero, mul_one]

/-- The destination and left core word are packed in one transition entry. -/
@[expose] public def destination (c : Nat) : Fin 3200 :=
  ⟨c % 4096 % 3200, Nat.mod_lt _ (by decide)⟩

/-- All fields are untrusted finite data; the transition equations certify them. -/
public structure Table where
  nodes : Fin 3200 → Nat
  transitions : Fin 2 → Fin 3200 → Nat

@[expose] public def Steps (i : Fin 2) (t : Table) : Prop :=
  ∀ (k : Fin 2) (r : Fin 3200),
    node i (t.nodes r) * standard (k.castLE (by decide)) =
      evalWord (signedCore i) (word (t.transitions k r / 4096)) *
        node i (t.nodes (destination (t.transitions k r)))

private theorem standard_closure : closure {standard 0, standard 1} = ⊤ := by
  let L : Subgroup Atlas1600Group := closure {standard 0, standard 1}
  have hle : atlas1600Subgroup ≤ L.map inclusion := by
    apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨standard 0, subset_closure (by simp), rfl⟩
    · have hg' : g = atlas1600B := hg
      subst g
      exact ⟨standard 1, subset_closure (by simp), rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (inclusion_injective he) ▸ hy

/-- Checked right transitions give the exhaustive literal double-coset cover. -/
public theorem cover_of_steps (i : Fin 2) (t : Table)
    (hzero : t.nodes 0 = 0) (hstep : Steps i t) (x : Atlas1600Group) :
    ∃ (a b : core (i.castLE (by decide))) (j : Fin 6),
      x = a.val * representative i j * b.val := by
  have hx : x ∈ Submonoid.closure {standard 0, standard 1} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, standard_closure]
    trivial
  have hfactor : ∃ (a : core (i.castLE (by decide))) (r : Fin 3200),
      x = a.val * node i (t.nodes r) := by
    induction hx using Submonoid.closure_induction_right with
    | one =>
      refine ⟨1, 0, ?_⟩
      simp only [OneMemClass.coe_one, hzero, node_zero, mul_one]
    | mul_right z hz g hg ih =>
      obtain ⟨a, r, hr⟩ := ih
      have hg' : ∃ k : Fin 2, g = standard (k.castLE (by decide)) := by
        rcases hg with rfl | hg
        · exact ⟨0, rfl⟩
        · exact ⟨1, hg⟩
      obtain ⟨k, rfl⟩ := hg'
      refine ⟨⟨a.val * evalWord (signedCore i) (word (t.transitions k r / 4096)),
        (core _).mul_mem a.property (word_mem _ _)⟩,
        destination (t.transitions k r), ?_⟩
      rw [hr, mul_assoc, hstep k r, ← mul_assoc]
  obtain ⟨a, r, hr⟩ := hfactor
  refine ⟨a, ⟨evalWord (signedCore i) (word (t.nodes r / 8)), word_mem _ _⟩,
    repIndex (t.nodes r), ?_⟩
  simpa only [node, mul_assoc] using hr

end Tits.MinimumIndexThirteen.CandidateRigidity.CoreCover
