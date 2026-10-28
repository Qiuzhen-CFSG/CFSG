module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.TreeData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.LocalEleven

/-!
# Extracting the unique degree-seven module from the eleven-block calculation

The natural-number incidence equations along the eleven-block path determine
the ten simple degrees successively. Together with the four defect-zero rows,
the degrees are `1,119,14,106,27,49,7,69,64,56,77,77,77,209`.
Only the seventh edge has degree seven. Trace coverage of the genuine family
on eleven-regular elements gives an actual intertwining equivalence to every
irreducible, so this degree count proves uniqueness on the required coordinate
space. No Maschke argument for the ambient group is used.

This assembly is conditional on the actual modular family. Establishing the
ordinary table and then this family from the local source hypotheses remains
necessary before asserting `UniqueClosedSeven G` for a source group.
Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*,
§16.6, p.482. The precise path specification is documented in
`ModularCharacters/Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- Integer dimensions, as opposed to trace residues, determine all edge degrees. -/
public theorem degree_eq_of_decompositionDegree {d : Fin 14 → ℕ}
    (h : decompositionDegree d = ordinaryDegree) :
    d = ![1, 119, 14, 106, 27, 49, 7, 69, 64, 56, 77, 77, 77, 209] := by
  have hh : ∀ i, decompositionDegree d i = ordinaryDegree i := congrFun h
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  have h5 := hh 5
  have h6 := hh 6
  have h7 := hh 7
  have h8 := hh 8
  have h9 := hh 9
  have h10 := hh 10
  have h11 := hh 11
  have h12 := hh 12
  have h13 := hh 13
  have h14 := hh 14
  dsimp [decompositionDegree, ordinaryDegree] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  funext i
  fin_cases i <;> dsimp <;> omega

/-- The incidence calculation has exactly one edge of degree seven. -/
public theorem ElevenTreeFamily.degree_seven_iff {G : Type*} [Group G]
    (b : ElevenTreeFamily G) (i : Fin 14) : b.degree i = 7 ↔ i = 6 := by
  rw [degree_eq_of_decompositionDegree b.degree_equations]
  fin_cases i <;> decide

private theorem exists_coordinate_transport {G : Type*} [Group G] {n m : ℕ}
    (h : n = m) (ρ : Representation ElevenClosure G (Fin n → ElevenClosure))
    (hρ : Representation.IsIrreducible ρ) :
    ∃ σ : Representation ElevenClosure G (Fin m → ElevenClosure),
      Representation.IsIrreducible σ ∧ Nonempty (ρ.Equiv σ) := by
  subst m
  exact ⟨ρ, hρ, ⟨Representation.Equiv.refl ρ⟩⟩

/-- Application of the genuine modular family to the published degree-seven
contract. Its existence still has to be proved from the source hypotheses. -/
public theorem uniqueClosedSeven_of_treeFamily {G : Type*} [Group G] [Finite G]
    (b : ElevenTreeFamily G) : UniqueClosedSeven G := by
  have hseven : b.degree 6 = 7 := (b.degree_seven_iff 6).mpr rfl
  obtain ⟨ρ, hρ, ⟨eρ⟩⟩ := exists_coordinate_transport hseven (b.rep 6) (b.irreducible 6)
  refine ⟨ρ, hρ, ?_⟩
  intro σ hσ
  let := hσ
  obtain ⟨i, hi⟩ := b.complete 7 σ hσ
  let := b.irreducible i
  obtain ⟨e⟩ := (Representation.pRegular_character_eq_iff_equiv_of_irreducible
    11 (b.rep i) σ).mp hi
  have hd : b.degree i = 7 := by
    simpa using e.toLinearEquiv.finrank_eq
  have he : i = 6 := (b.degree_seven_iff i).mp hd
  subst i
  exact ⟨eρ.symm.trans e⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
