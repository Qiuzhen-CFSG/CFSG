module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.DefectZero.TraceSeparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.DefectZero.IntegralConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.DefectZero.Irreducibility

/-!
# The four characteristic-eleven defect-zero modules

The genuine ordinary rows 5, 6, 7 and 14 admit compatible integral models
on coordinate spaces of dimensions 77, 77, 77 and 209. Their reductions land
in the literal `ElevenClosure`. The source order 175560 makes each degree
cofactor prime to eleven, so matrix-coefficient orthogonality proves that
these reductions are irreducible. Compatible involution and fifth-root
traces distinguish the three degree-77 modules; natural dimension separates
the degree-209 module.

`exists_defectZeroModules` discharges the defect-zero realization contract
using only the ordinary data and group order. Construction of the ordinary
data and the ten path modules remains with their separate source arguments.
Source: Feit, *The Representation Theory of Finite Groups*, IV.4.19–20,
pp.159–160; Janko, J. Algebra 3 (1966), 147–186.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero

variable {G R : Type*} [Group G] [Finite G] [CommRing R] [IsDomain R]
  {d : OrdinaryData G}

/-- Assemble the four actual reductions after their irreducibility is supplied.
Trace separation discharges the nontrivial inequivalence clause. -/
public noncomputable def IntegralModels.toDefectZeroModules (m : IntegralModels d R)
    (hirr : ∀ i, Representation.IsIrreducible (m.reduction i)) : DefectZeroModules G where
  rep := m.reduction
  irreducible := hirr
  inequivalent := m.reductions_inequivalent

/-- The four defect-zero ordinary rows give pairwise inequivalent irreducible
modules of dimensions 77, 77, 77 and 209 over `ElevenClosure`. All integral
models and their reduction properties are constructed from the ordinary data
and source order; no local-centralizer or simplicity hypothesis is needed. -/
public theorem exists_defectZeroModules (d : OrdinaryData G)
    (horder : Nat.card G = 175560) : Nonempty (DefectZeroModules G) := by
  obtain ⟨S, hSring, hSdomain, ⟨m⟩⟩ := exists_integralModels d horder
  let := hSring
  let := hSdomain
  exact ⟨m.toDefectZeroModules (m.reductions_irreducible horder)⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero
