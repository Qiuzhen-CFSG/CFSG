module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.Data
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F00
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F01
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F02
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F03
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F04
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F05
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F06
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F07
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F10
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F11
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F12
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F13
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F14
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F15
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F16
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.F17
import Mathlib.Tactic.FinCases

/-!
# Full matrix algebras on the Hermitian induction factors

Each of the sixteen literal diagonal blocks generates its entire binary matrix
algebra. Separate rank-one and orbit-basis certificates establish this for every
block, including both 98-dimensional blocks; equal dimensions do not identify
representations. The result is exactly the density input to
`filtration_of_flag_matrices` and `filtration_of_generator_coordinates`.
The actual representation comparison and filtration assembly are independent.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16, and
Aschbacher--Smith Chapter K, pp.451--452,457. Reproducible witness discovery and
certificate generation are retained in `FactorAlgebras/source/`.
-/

@[expose] public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration

/-- The two generators of every literal factor generate its full matrix algebra. -/
theorem fullFactorAlgebra (i : Fin 2) (t : Factor)
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree i t)) (Fin (degree i t)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix i t j ∈ Q) : Q = ⊤ := by
  fin_cases i <;> fin_cases t
  · exact FactorAlgebras.F00.full Q hA
  · exact FactorAlgebras.F01.full Q hA
  · exact FactorAlgebras.F02.full Q hA
  · exact FactorAlgebras.F03.full Q hA
  · exact FactorAlgebras.F04.full Q hA
  · exact FactorAlgebras.F05.full Q hA
  · exact FactorAlgebras.F06.full Q hA
  · exact FactorAlgebras.F07.full Q hA
  · exact FactorAlgebras.F10.full Q hA
  · exact FactorAlgebras.F11.full Q hA
  · exact FactorAlgebras.F12.full Q hA
  · exact FactorAlgebras.F13.full Q hA
  · exact FactorAlgebras.F14.full Q hA
  · exact FactorAlgebras.F15.full Q hA
  · exact FactorAlgebras.F16.full Q hA
  · exact FactorAlgebras.F17.full Q hA

/-- In particular the actual generated subalgebra is the whole endomorphism algebra. -/
theorem adjoin_factorMatrix_eq_top (i : Fin 2) (t : Factor) :
    Algebra.adjoin (ZMod 2) (Set.range (factorMatrix i t)) = ⊤ :=
  fullFactorAlgebra i t _ fun j => Algebra.subset_adjoin (Set.mem_range_self j)

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
