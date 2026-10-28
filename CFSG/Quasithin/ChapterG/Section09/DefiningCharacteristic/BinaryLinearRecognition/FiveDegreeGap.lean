module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.EndpointAdjacent
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case0
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case1
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case2
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case3
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case02
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case03
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case12
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case13

/-!
# The faithful binary SL₅ degree gap through fourteen

Every nonzero finite-dimensional binary representation has a local highest
vector, obtained from the zero-Hecke action on upper-unitriangular invariants.
Faithfulness and irreducibility exclude empty support. A singleton support gives
exactly five or ten dimensions: its independent permutation translates span an
invariant subspace. Every larger support gives at least fifteen independent
vectors (sixteen when it contains an endpoint-adjacent pair).

Consequently a faithful irreducible binary representation of the actual matrix
group SL₅(2), of degree at most fourteen, has degree five or ten. The canonical
`SL5TenDimensional.projectiveEquiv` in `Models` identifies this group with PSL₅(2).
No absolute irreducibility or degree-ten module identification is used.

This supplies the degree-only input to G.9.3(13), Aschbacher--Smith, combined
manuscript (1 March 2004), printed pp.354,356–357/PDF pp.365,367–368. The cited
source's next degree is 24; only exclusion through fourteen is needed here.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap

open Representation Representation.SL5TenDimensional
open Representation.SL5TenDimensional.Classification

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem multiple_support_cases (J : Finset (Fin 4)) (hJ : 2 ≤ J.card) :
    (0 ∈ J ∧ 1 ∈ J) ∨ (2 ∈ J ∧ 3 ∈ J) ∨
      J = {0, 2} ∨ J = {0, 3} ∨ J = {1, 2} ∨ J = {1, 3} := by
  revert J
  decide +kernel

/-- Every support of size at least two exceeds the degree-fourteen cutoff. -/
theorem fifteen_le_finrank_of_multiple [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) (hJ : 2 ≤ J.card) :
    15 ≤ Module.finrank (ZMod 2) V := by
  rcases multiple_support_cases J hJ with ⟨h0, h1⟩ | ⟨h2, h3⟩ | rfl | rfl | rfl | rfl
  · have hh := EndpointAdjacent.sixteen_le_finrank h hv h0 h1 (by decide) (Or.inl rfl)
    omega
  · have hh := EndpointAdjacent.sixteen_le_finrank h hv h2 h3 (by decide) (Or.inr rfl)
    omega
  · exact Case02.degree_le h hv
  · exact Case03.degree_le h hv
  · exact Case12.degree_le h hv
  · exact Case13.degree_le h hv

/-- Singleton highest-vector support has degree five or ten. -/
theorem finrank_eq_five_or_ten_of_singleton [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ] {i : Fin 4} {v : V}
    (h : LocalHighestVector ρ {i} v) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) V = 5 ∨ Module.finrank (ZMod 2) V = 10 := by
  fin_cases i
  · exact Or.inl (Case0.finrank_eq h hv)
  · exact Or.inr (Case1.finrank_eq h hv)
  · exact Or.inr (Case2.finrank_eq h hv)
  · exact Or.inl (Case3.finrank_eq h hv)

/-- The exact degree-gap input to `five_alternatives_of_degree_gap`: faithful
irreducible binary SL₅ modules of degree at most fourteen have degree five or ten. -/
theorem finrank_eq_five_or_ten [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (hd : Module.finrank (ZMod 2) V ≤ 14) :
    Module.finrank (ZMod 2) V = 5 ∨ Module.finrank (ZMod 2) V = 10 := by
  let : IsIrreducible ρ := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J, v, hv, h⟩ := exists_localHighestVector ρ
  have hpos := Finset.card_pos.mpr (support_nonempty hf hv h)
  have hcard : J.card = 1 := by
    by_contra hn
    have hh := fifteen_le_finrank_of_multiple h hv (by omega)
    omega
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  exact finrank_eq_five_or_ten_of_singleton h hv

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap
