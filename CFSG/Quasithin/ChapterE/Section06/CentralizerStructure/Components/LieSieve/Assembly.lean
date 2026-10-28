module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic

/-!+# The adequate characteristic-two component sieve for E.6.8

The invariant-parabolic reduction in `OtherTypes` leaves the Bender models,
PSL₃ models and their permitted central two-covers, both symplectic constructors,
and the actual S₈ quotient branch. The corresponding family theorems supply
every Borel and symplectic clause. Within the Bender case, PSL₂(4) is handled
separately: the source explicitly regards it as PSL₂(5), and its odd branch
has both action corank and global rank one.

`adequate_alternatives` preserves the complete Borel and symplectic records.
Its linear-four and odd tuples omit only the assertion U = C_V(L) from the
full records; that assertion is not inferred from the action corank. The odd
model is on L itself and retains its Fermat/Mersenne restriction. These explicit
tuples can be consumed by the parent E.6.8 assembly without a shared definition
dependency. `full_alternatives_to_adequate` records the separate conversion
from the unchanged full records.

The only earlier-source inputs are `EarlierLocalFacts`, the universally
quantified full `E67Input`, and the full relative-normality alternative of
1.2.1(3). Their discharge belongs to the parent source assembly. No model
exclusion, Borel placement, action calculation, or fixed-space equality is
assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and 1.2.1(3), printed p.504
(PDF p.521).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve
open Chapter1.Section02.LocalModels InvariantSubspaces.BlockSelection

variable {G : Type*} [Group G]
variable {M V U Q L : Subgroup G}

/-- Forget only the two fixed-space fields in the full four-way alternatives.
This conversion does not assert that either fixed-space equality is available
under the source hypotheses. -/
theorem full_alternatives_to_adequate
    (ha : (∃ n, BorelAlternative M V U L n) ∨
      (∃ n, SymplecticAlternative M V U L n) ∨
      LinearFourAlternative M V U Q L ∨ OddAlternative M V U L) :
    (∃ n, BorelAlternative M V U L n) ∨
      (∃ n, SymplecticAlternative M V U L n) ∨
      (ClassicalGroup.IsPSL L 4 2 ∧
        Nonempty ((↥(L ⊔ Q) ⧸ pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8)) ∧
        actionCorank V L = 1 ∧ globalR V = 1) ∨
      (((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
        ClassicalGroup.IsPSL L 3 3 ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)) ∧
        actionCorank V L = 1 ∧ globalR V = 1) := by
  rcases ha with hB | hS | h4 | hodd
  · exact Or.inl hB
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl ⟨h4.model, h4.quotient, h4.dimension, h4.global_rank⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hodd.model, hodd.dimension, hodd.global_rank⟩))

variable [Finite G] {T : Sylow 2 G}

/-- The adequate four-way Lie-type sieve under genuine Hypothesis E.6.1.
It handles every `LieTypeComponent` constructor, retaining central covers,
Sp₄(2)′, the literal S₈ quotient, and the exceptional PSL₂(4) odd outcome.
Only the permitted earlier universal source statements remain explicit. -/
theorem adequate_alternatives
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (earlier : EarlierLocalFacts T) (h67 : E67Input T M V)
    (h121 : ∀ H : Subgroup G, H ∈ Chapter1.H G → ∀ B : Subgroup H,
      B.IsCComponent → B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hU : U ∈ obstructionFamily M V)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : LieTypeComponent L) :
    (∃ n, BorelAlternative M V U L n) ∨
      (∃ n, SymplecticAlternative M V U L n) ∨
      (ClassicalGroup.IsPSL L 4 2 ∧
        Nonempty ((↥(L ⊔ Q) ⧸ pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8)) ∧
        actionCorank V L = 1 ∧ globalR V = 1) ∨
      (((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
        ClassicalGroup.IsPSL L 3 3 ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)) ∧
        actionCorank V L = 1 ∧ globalR V = 1) := by
  rcases OtherTypes.lieType_reduction h earlier hU hL hQ h67 h121 hm with
    hB | ⟨n, hn, h3⟩ | ⟨n, hn, hS⟩ | hS | ⟨hz, h3⟩ | h4
  · by_cases hfour : ClassicalGroup.IsPSL L 2 4
    · rcases ExceptionalBranch.adequate_borel_or_odd h earlier h67 hU hL hfour with
        hb | ⟨hmodel, hdim, hrank⟩
      · exact Or.inl hb
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inl hmodel, hdim, hrank⟩))
    · exact Or.inl (RankOne.exists_borelAlternative h earlier h67 hU hL hB hfour)
  · exact Or.inl ⟨n, LinearThree.ordinary_borelAlternative h earlier h67 hU hL hn h3⟩
  · exact Or.inr (Or.inl ⟨n, Symplectic.projective_alternative h earlier h67 hU hL hn hS⟩)
  · exact Or.inr (Or.inl ⟨1, Symplectic.projective_derived_alternative h earlier hU hL hS⟩)
  · exact Or.inl ⟨2, LinearThree.cover_borelAlternative h earlier h67 hU hL rfl hz h3⟩
  · exact Or.inr (Or.inr (Or.inl h4))

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve
