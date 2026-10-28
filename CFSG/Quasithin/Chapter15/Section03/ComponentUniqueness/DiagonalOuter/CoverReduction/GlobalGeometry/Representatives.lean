module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses

/-!
# The representative on the fixed line

An order-two intersection Z_S ∩ V₁ has a nonidentity generator. Since Z_S
centralizes S, that generator is centralized by S. The output interface below
also retains the global centralizer bound and the actual subgroup
acting transitively on the punctured plane.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.3.38, printed pp.1136--1137. The global centralizer assertion
requires the component-embedding argument; it is not proved by this interface.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
variable {G : Type*} [Group G]

/-- Output of the embedding argument, constructed in `GlobalGeometry.Assembly`.
Both the chosen line and the transitive actor are embedded in G. -/
structure RepresentativeGeometry (V ZS S I : Subgroup G) where
  v : G
  ne_one : v ≠ 1
  order : orderOf v = 2
  generator : zpowers v = ZS ⊓ V
  sylow_centralizes : S ≤ centralizer ({v} : Set G)
  centralizer_le : centralizer ({v} : Set G) ≤ I
  actor : Subgroup G
  actor_le : actor ≤ I
  transitive : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
    ∃ m : actor, (MulAut.conj (m : G)) x = y

/-- Choose the nonidentity generator of the actual fixed line, with its
order and centralization by S proved, not independently specified. -/
theorem exists_fixed_line_generator [Finite G] (V ZS S : Subgroup G)
    (hZS : ZS ≤ centralizer (S : Set G)) (hcard : Nat.card (ZS ⊓ V : Subgroup G) = 2) :
    ∃ v : G, v ≠ 1 ∧ orderOf v = 2 ∧ zpowers v = ZS ⊓ V ∧
      S ≤ centralizer ({v} : Set G) := by
  have hne : ZS ⊓ V ≠ ⊥ := by
    intro he
    rw [he] at hcard
    norm_num at hcard
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ ZS ⊓ V, v ≠ 1 := by
    by_contra! h
    exact hne ((ZS ⊓ V).eq_bot_iff_forall.mpr h)
  have ho : orderOf v = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _
      (hcard ▸ (ZS ⊓ V).orderOf_dvd_natCard hv) with h | h
    · exact (hv1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  refine ⟨v, hv1, ho, eq_of_le_of_card_ge (zpowers_le_of_mem hv) ?_, ?_⟩
  · rw [Nat.card_zpowers, ho, hcard]
  · intro s hs
    exact mem_centralizer_singleton_iff.mpr (hZS hv.1 s hs)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
