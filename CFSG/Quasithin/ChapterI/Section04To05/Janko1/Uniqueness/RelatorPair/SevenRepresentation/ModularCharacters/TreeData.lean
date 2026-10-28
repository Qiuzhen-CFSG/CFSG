module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularInput
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryData
public import Theory.Representation.IrreduciblePRegularEquivalence

/-!
# The genuine modular family required by the eleven-block argument

The principal-block path, in zero-based ordinary row labels, is
`0–8–12–10–11–3–2–4–13–9–1`. Its ten edges label simple modules.
The remaining four ordinary rows, `5,6,7,14`, have defect zero.
The incidence equations below retain natural dimensions, rather than their
residues modulo eleven. The family consists of actual irreducible modules;
trace coverage on eleven-regular elements will supply actual equivalences.

Existence of this family from the source group's ordinary table remains an
unproved prerequisite. In particular, the path for the ATLAS model is not a
proof that the arbitrary source group has the same modular representations.
Source specification: GAP CTblLib 1.3.11 `data/ctbconja.tbl`, `J1` at 11,
Thomas Breuer, GPL-3.0-or-later; see `Source.md` in this directory.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- Dimensions of the reductions of the fifteen ordinary rows, obtained from
the path incidence matrix and the four defect-zero rows. -/
@[expose] public def decompositionDegree (d : Fin 14 → ℕ) : Fin 15 → ℕ :=
  ![d 0, d 9, d 5 + d 6, d 4 + d 5, d 6 + d 7, d 10, d 11, d 12,
    d 0 + d 1, d 8 + d 9, d 2 + d 3, d 3 + d 4, d 1 + d 2,
    d 7 + d 8, d 13]

/-- Actual simple modules and the conclusions needed from the Brauer-tree
calculation. This is an explicit prerequisite, not an existence theorem. -/
public structure ElevenTreeFamily (G : Type*) [Group G] where
  degree : Fin 14 → ℕ
  rep : ∀ i, Representation ElevenClosure G (Fin (degree i) → ElevenClosure)
  irreducible : ∀ i, Representation.IsIrreducible (rep i)
  degree_equations : decompositionDegree degree = ordinaryDegree
  complete : ∀ (n : ℕ) (σ : Representation ElevenClosure G (Fin n → ElevenClosure)),
    Representation.IsIrreducible σ → ∃ i, ∀ g : G, ¬ 11 ∣ orderOf g →
      (rep i).character g = σ.character g

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
