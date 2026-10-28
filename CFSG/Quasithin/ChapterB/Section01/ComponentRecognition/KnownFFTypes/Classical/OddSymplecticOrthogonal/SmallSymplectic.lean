module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.RankOne

/-!
# The small odd rank-one symplectic quotients

The actual PSp₂–PSL₂ equivalence descends through the literal centers.
Composing with the concrete exceptional isomorphisms identifies the
q = 5, 7, 9 quotients with A₅, PSL₃(2), A₆ respectively. These three
permitted catalogue entries therefore satisfy the quotient alternative
without any representation or covering hypothesis.

This closes the small rank-one symplectic entries in the classical branch
of Aschbacher–Smith B.1.13, printed pp.73–74. The remaining parameters
still require the full-normalizer FF exclusion; rank two is not omitted.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal
universe u
variable {L : Type u} [Group L]

/-- The rank-one symplectic catalogue uses the same actual simple carrier as PSL₂. -/
theorem isPSL_of_isPSp_rankOne {G : Type u} [Group G] {q : ℕ}
    (h : ClassicalGroup.IsPSp G 1 q) : ClassicalGroup.IsPSL G 2 q := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    ⟨e.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv⟩⟩

/-- The literal rank-one symplectic parameter predicate supplies exactly
its linear counterpart, including the exclusions q = 2, 3. -/
theorem linearParameters_of_symplectic_rankOne {q : ℕ}
    (hp : KnownSimple.SymplecticParameters 1 q) : KnownSimple.LinearParameters 2 q :=
  ⟨hp.1, by decide, fun _ => hp.2.2.1 rfl⟩

/-- Apply any independently proved PSL₂ quotient recognition to the
rank-one symplectic branch, using both the actual carrier map and exact parameters. -/
theorem quotientAlternative_of_psp_rankOne_of_linear {q : ℕ}
    (hp : KnownSimple.SymplecticParameters 1 q)
    (h : ClassicalGroup.IsPSp (L ⧸ center L) 1 q)
    (hlinear : KnownSimple.LinearParameters 2 q →
      ClassicalGroup.IsPSL (L ⧸ center L) 2 q → QuotientAlternative L) :
    QuotientAlternative L :=
  hlinear (linearParameters_of_symplectic_rankOne hp) (isPSL_of_isPSp_rankOne h)

/-- The three small odd PSL₂ quotients have actual alternating or even-field carriers. -/
theorem quotientAlternative_of_psl2_small {q : ℕ}
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q)
    (hq : q = 5 ∨ q = 7 ∨ q = 9) : QuotientAlternative L := by
  rcases hq with rfl | rfl | rfl
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : Fintype F := Fintype.ofFinite F
    let f : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
    exact Or.inr ⟨5, by decide,
      ⟨(e.trans (Atlas.fieldEquivPSL 2 f)).trans
        Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩⟩
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    have hp : KnownSimple.LinearParameters 3 2 := by
      exact ⟨(isPrimePow_nat_iff 2).mpr ⟨2, 1, by decide, by decide, by decide⟩,
        by decide, by omega⟩
    exact Or.inl (.classical 2 (by decide) (.linear 3 hp
      ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
        ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hc)⟩⟩))
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    exact Or.inr ⟨6, by decide,
      ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hc)⟩⟩

/-- Retain and recognize all three small odd rank-one symplectic aliases. -/
theorem quotientAlternative_of_psp_rankOne_small {q : ℕ}
    (h : ClassicalGroup.IsPSp (L ⧸ center L) 1 q)
    (hq : q = 5 ∨ q = 7 ∨ q = 9) : QuotientAlternative L :=
  quotientAlternative_of_psl2_small (isPSL_of_isPSp_rankOne h) hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal
