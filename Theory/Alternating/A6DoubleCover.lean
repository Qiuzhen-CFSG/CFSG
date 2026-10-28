module

import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.GroupTheory.CommutingProbability
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public import Theory.Alternating.proposition_5_2_6
public import Theory.GroupTheory.WordSubgroup
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.A6DoubleCoverOrderData -/
open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open scoped Pointwise

@[reducible, expose] public def a6ChainGen0 : Fin 4 → Perm144 :=
  fun i => Vector.get #v[a6DoubleCoverGen1, a6DoubleCoverGen1⁻¹,
    a6DoubleCoverGen2, a6DoubleCoverGen2⁻¹] i

@[reducible, expose] public def a6ChainInv0 : Fin 4 → Fin 4 := ![1, 0, 3, 2]

public theorem a6ChainInv0_spec (i : Fin 4) :
    a6ChainGen0 (a6ChainInv0 i) = (a6ChainGen0 i)⁻¹ := by
  decide +revert +kernel

@[reducible, expose] public def a6ChainRepWord0 : Fin 144 → List (Fin 4) :=
  fun i => Vector.get #v[[], [(2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(2 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(0 : Fin 4), (2 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (3 : Fin 4), (1 : Fin 4), (1 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (1 : Fin 4), (3 : Fin 4), (0 : Fin 4), (3 : Fin 4)], [(2 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (3 : Fin 4), (0 : Fin 4), (2 : Fin 4)], [(3 : Fin 4), (0 : Fin 4), (3 : Fin 4), (1 : Fin 4), (3 : Fin 4)]] i

@[reducible, expose] public def a6ChainRep0 (r : Fin 144) : Perm144 :=
  evalWord a6ChainGen0 (a6ChainRepWord0 r)

@[reducible, expose] public def a6ChainGen1 : Fin 2 → Perm144 :=
  fun i => Vector.get #v[a6DoubleCoverGen1, a6DoubleCoverGen1⁻¹] i

@[reducible, expose] public def a6ChainInv1 : Fin 2 → Fin 2 := ![1, 0]

public theorem a6ChainInv1_spec (i : Fin 2) :
    a6ChainGen1 (a6ChainInv1 i) = (a6ChainGen1 i)⁻¹ := by
  decide +revert +kernel

@[reducible, expose] public def a6ChainFactor0 : Fin 4 → Fin 144 → List (Fin 2)
  | 0 => fun i => Vector.get #v[[(0 : Fin 2)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [(1 : Fin 2), 1], [], [], [], [], [], [(0 : Fin 2)], [], [], [], [], [], [(0 : Fin 2)], [], [], [(0 : Fin 2)], [], [(0 : Fin 2), 0], [], [(0 : Fin 2)], [], [], [], [(0 : Fin 2)], [], [], [(0 : Fin 2)], [], [], [], [], [(0 : Fin 2), 0], [], [(1 : Fin 2)], [(0 : Fin 2), 0], [(0 : Fin 2), 0], [(0 : Fin 2)], [], [(1 : Fin 2), 1], [], [], [(1 : Fin 2)], [], [], [], [], [(1 : Fin 2), 1], [], [(1 : Fin 2), 1], [], [(1 : Fin 2)], [(1 : Fin 2)], [], [(0 : Fin 2), 0], [(0 : Fin 2)], [], [(0 : Fin 2)], [(0 : Fin 2)], [], [(0 : Fin 2)], [(0 : Fin 2)], [(1 : Fin 2), 1], [], [(1 : Fin 2)], [(1 : Fin 2), 1], [], [(0 : Fin 2), 0], [], [], [(0 : Fin 2)], [(0 : Fin 2)], [], [(0 : Fin 2), 0], [(0 : Fin 2)], [(1 : Fin 2)], [], [(1 : Fin 2), 1], [], [], [], [(1 : Fin 2), 1], [(0 : Fin 2), 0], [], [(1 : Fin 2)], [], [(1 : Fin 2)], [(1 : Fin 2)], [], [], [(1 : Fin 2)], [], [(0 : Fin 2)], [], [], [], [(1 : Fin 2)], [(0 : Fin 2), 0], [(0 : Fin 2), 0], [(0 : Fin 2)], [(1 : Fin 2)], []] i
  | 1 => fun i => Vector.get #v[[(1 : Fin 2)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [(0 : Fin 2), 0], [], [], [], [], [(1 : Fin 2)], [], [(1 : Fin 2)], [], [], [(1 : Fin 2)], [], [], [(1 : Fin 2)], [(1 : Fin 2), 1], [], [], [], [(1 : Fin 2), 1], [], [], [], [], [], [], [(0 : Fin 2), 0], [(0 : Fin 2), 0], [], [], [(0 : Fin 2)], [], [(1 : Fin 2), 1], [], [], [], [], [], [], [], [], [], [], [(0 : Fin 2)], [(1 : Fin 2), 1], [(1 : Fin 2)], [], [(0 : Fin 2)], [], [(1 : Fin 2), 1], [], [], [(1 : Fin 2)], [(1 : Fin 2)], [], [], [], [], [], [], [(1 : Fin 2), 1], [(1 : Fin 2)], [(0 : Fin 2)], [(1 : Fin 2)], [(1 : Fin 2)], [(1 : Fin 2)], [], [], [], [(0 : Fin 2), 0], [], [(0 : Fin 2), 0], [(0 : Fin 2)], [(0 : Fin 2)], [(0 : Fin 2)], [(0 : Fin 2), 0], [], [(1 : Fin 2)], [], [(0 : Fin 2)], [], [], [], [(0 : Fin 2)], [], [(1 : Fin 2)], [(1 : Fin 2), 1], [(1 : Fin 2)], [(0 : Fin 2)], [(1 : Fin 2), 1], [(0 : Fin 2), 0], [], [(0 : Fin 2), 0], [], [(1 : Fin 2)], [(1 : Fin 2), 1], [(1 : Fin 2)], [(0 : Fin 2)], [], [], [(1 : Fin 2), 1], [(0 : Fin 2)], [(1 : Fin 2)]] i
  | 2 => fun i => Vector.get #v[[], [], [], [], [], [], [], [(0 : Fin 2), 0], [], [], [], [(1 : Fin 2), 1], [], [], [(0 : Fin 2)], [], [(1 : Fin 2)], [(1 : Fin 2), 1], [], [], [], [(1 : Fin 2)], [], [], [(1 : Fin 2)], [], [], [], [], [], [(0 : Fin 2), 0], [], [], [], [], [(0 : Fin 2), 0], [], [(0 : Fin 2)], [], [], [], [(0 : Fin 2)], [(1 : Fin 2)], [], [], [], [], [(0 : Fin 2)], [], [(1 : Fin 2), 1], [], [], [], [], [], [], [(1 : Fin 2), 1], [(0 : Fin 2)], [], [], [], [], [], [], [(1 : Fin 2)], [], [], [], [], [], [(0 : Fin 2), 0], [], [], [], [(1 : Fin 2), 1], [(0 : Fin 2)], [], [(0 : Fin 2), 0], [(0 : Fin 2)], [(1 : Fin 2), 1], [], [(1 : Fin 2)], [], [], [(1 : Fin 2), 1], [], [], [], [], [], [(1 : Fin 2), 1], [], [], [], [], [(0 : Fin 2)], [(1 : Fin 2), 1], [], [], [], [(0 : Fin 2), 0], [], [], [], [], [(1 : Fin 2), 1], [], [(1 : Fin 2)], [], [], [(1 : Fin 2)], [], [], [], [(0 : Fin 2), 0], [], [], [(1 : Fin 2)], [], [(0 : Fin 2)], [(0 : Fin 2), 0], [(0 : Fin 2)], [], [], [], [], [], [], [], [(1 : Fin 2), 1], [], [(1 : Fin 2)], [(0 : Fin 2)], [], [(1 : Fin 2), 1], [], [], [], [(1 : Fin 2)], [(0 : Fin 2), 0], [], [], [(0 : Fin 2)], []] i
  | 3 => fun i => Vector.get #v[[], [], [], [], [], [], [], [], [], [(1 : Fin 2), 1], [], [(1 : Fin 2), 1], [], [], [(0 : Fin 2)], [], [(1 : Fin 2)], [], [], [], [(0 : Fin 2), 0], [], [], [], [], [(1 : Fin 2)], [], [], [(0 : Fin 2)], [(1 : Fin 2), 1], [(0 : Fin 2), 0], [], [], [], [], [], [], [(0 : Fin 2)], [], [], [], [(0 : Fin 2)], [], [], [], [], [], [], [], [], [], [], [], [], [(1 : Fin 2), 1], [], [(1 : Fin 2), 1], [], [], [], [(1 : Fin 2)], [], [], [(1 : Fin 2), 1], [(1 : Fin 2)], [], [(1 : Fin 2)], [], [], [], [(0 : Fin 2), 0], [], [], [], [], [(0 : Fin 2)], [], [(0 : Fin 2), 0], [(1 : Fin 2)], [(0 : Fin 2), 0], [], [(1 : Fin 2)], [], [], [], [(0 : Fin 2), 0], [], [], [], [], [], [(0 : Fin 2)], [], [], [], [(0 : Fin 2)], [(1 : Fin 2), 1], [], [], [(1 : Fin 2), 1], [(0 : Fin 2), 0], [], [(1 : Fin 2)], [], [], [(1 : Fin 2)], [(0 : Fin 2)], [(0 : Fin 2), 0], [], [], [(1 : Fin 2)], [], [], [(0 : Fin 2)], [(0 : Fin 2), 0], [], [], [(1 : Fin 2)], [], [], [(0 : Fin 2), 0], [], [], [], [], [(1 : Fin 2)], [(0 : Fin 2), 0], [], [], [], [(1 : Fin 2), 1], [], [(0 : Fin 2), 0], [(0 : Fin 2)], [(0 : Fin 2)], [], [], [], [], [], [], [], [], []] i


@[reducible, expose] public def a6ChainRepWord1 : Fin 5 → List (Fin 2) :=
  fun i => Vector.get #v[[], [(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), (0 : Fin 2)], [(1 : Fin 2), (1 : Fin 2)]] i

@[reducible, expose] public def a6ChainRep1 (r : Fin 5) : Perm144 :=
  evalWord a6ChainGen1 (a6ChainRepWord1 r)

@[reducible, expose] public def a6ChainAct1 : Fin 2 → Fin 5 → Fin 5
  | 0 => fun i => Vector.get #v[1, 3, 0, 4, 2] i
  | 1 => fun i => Vector.get #v[2, 0, 4, 1, 3] i

@[reducible, expose] public def a6ChainPoint1 : Fin 5 → Fin 144 := ![1, 2, 13, 4, 7]


end GLS3.Chapter5

namespace GLS3.Chapter5

abbrev A6F9 := QuadraticAlgebra (ZMod 3) (2 : ZMod 3) 0

local instance : Fact (∀ r : ZMod 3, r ^ 2 ≠ (2 : ZMod 3) + 0 * r) := ⟨by decide⟩

noncomputable local instance : Fintype A6F9 :=
  Fintype.ofEquiv ((ZMod 3) × (ZMod 3))
    (QuadraticAlgebra.equivProd (2 : ZMod 3) 0).symm

abbrev A6SL := Matrix.SpecialLinearGroup (Fin 2) A6F9

private def f9 (a b : ZMod 3) : A6F9 := ⟨a, b⟩

private def a6SLGen1 : A6SL := ⟨!![f9 0 0, f9 1 0; f9 2 0, f9 1 1], by decide⟩
private def a6SLGen2 : A6SL := ⟨!![f9 1 0, f9 0 0; f9 2 0, f9 1 0], by decide⟩

private def a6SLEquivDetKer : A6SL ≃*
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) A6F9 →* A6F9ˣ).ker where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g, by simp⟩
  invFun g := ⟨(g.1 : Matrix (Fin 2) (Fin 2) A6F9), by
    exact Units.ext_iff.mp (MonoidHom.mem_ker.mp g.2)⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' g h := by apply Subtype.ext; apply Units.ext; rfl

private theorem a6SL_card : Nat.card A6SL = 720 := by
  have hGL := Matrix.card_GL_field (𝔽 := A6F9) 2
  have hdet := GLS3.Chapter5.SchurPresentation.card_comap_mul
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) A6F9 →* A6F9ˣ)
    Matrix.GeneralLinearGroup.det_surjective (⊤ : Subgroup A6F9ˣ)
  have hker : Nat.card
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) A6F9 →* A6F9ˣ).ker =
      Nat.card A6SL := Nat.card_congr a6SLEquivDetKer.symm.toEquiv
  rw [show (⊤ : Subgroup A6F9ˣ).comap
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) A6F9 →* A6F9ˣ) = ⊤ by rfl,
    Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_units, hker] at hdet
  norm_num [Fintype.card_congr (QuadraticAlgebra.equivProd (2 : ZMod 3) 0),
    Matrix.card_GL_field] at hGL hdet ⊢
  omega

private theorem a6SLGen1_ne_one : a6SLGen1 ≠ 1 := by
  intro h
  have := congrArg (fun g : A6SL => (g : Matrix (Fin 2) (Fin 2) A6F9) 0 0) h
  exact zero_ne_one this

private theorem a6SLGen1_order : orderOf a6SLGen1 = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime (by
    apply Subtype.ext
    ext i j <;> fin_cases i <;> fin_cases j <;> decide) a6SLGen1_ne_one

private def a6SLStabilizer : Subgroup A6SL := Subgroup.zpowers a6SLGen1

private theorem a6SLStabilizer_card : Nat.card a6SLStabilizer = 5 := by
  rw [a6SLStabilizer, Nat.card_zpowers, a6SLGen1_order]

@[reducible] private def a6SLChainGen : Fin 4 → A6SL :=
  fun i => Vector.get #v[a6SLGen1, a6SLGen1⁻¹, a6SLGen2, a6SLGen2⁻¹] i

@[reducible] private def a6SLChainGen1 : Fin 2 → A6SL :=
  fun i => Vector.get #v[a6SLGen1, a6SLGen1⁻¹] i

@[reducible] private def a6SLRep (r : Fin 144) : A6SL :=
  Theory.GroupTheory.evalWord a6SLChainGen (a6ChainRepWord0 r)

@[reducible] private def a6SLNormalForm (x : Fin 144 × Fin 5) : A6SL :=
  a6SLRep x.1 * a6SLGen1 ^ x.2.val

@[reducible] private def a6F9Code (x : A6F9) : Nat :=
  x.re.val + 3 * x.im.val

@[reducible] private def a6SLCode (x : A6SL) : Nat :=
  a6F9Code (x.1 0 0) + 9 * a6F9Code (x.1 0 1) +
    81 * a6F9Code (x.1 1 0) + 729 * a6F9Code (x.1 1 1)

@[reducible] private def a6SLNormalPair (n : Fin 720) : Fin 144 × Fin 5 :=
  (⟨n.val / 5, by omega⟩, ⟨n.val % 5, Nat.mod_lt _ (by omega)⟩)

@[reducible] private def a6SLNormalIndex (x : Fin 144 × Fin 5) : Fin 720 :=
  ⟨x.1.val * 5 + x.2.val, by omega⟩

private theorem a6SLNormalPair_index (x : Fin 144 × Fin 5) :
    a6SLNormalPair (a6SLNormalIndex x) = x := by
  apply Prod.ext <;> apply Fin.ext <;> simp
  omega

private theorem a6SLNormalIndex_pair (n : Fin 720) :
    a6SLNormalIndex (a6SLNormalPair n) = n := by
  apply Fin.ext
  simp
  omega

private theorem a6SLNormalIndex_injective : Function.Injective a6SLNormalIndex := by
  intro x y h
  have := congrArg a6SLNormalPair h
  simpa only [a6SLNormalPair_index] using this

private def a6SLDecode : Nat → Fin 720
  | 730 => 0
  | 3087 => 1
  | 6518 => 2
  | 1862 => 3
  | 103 => 4
  | 892 => 5
  | 2358 => 6
  | 3440 => 7
  | 2915 => 8
  | 1237 => 9
  | 3494 => 10
  | 3593 => 11
  | 4335 => 12
  | 4976 => 13
  | 3903 => 14
  | 811 => 15
  | 3816 => 16
  | 605 => 17
  | 5183 => 18
  | 1885 => 19
  | 5875 => 20
  | 2555 => 21
  | 4913 => 22
  | 3220 => 23
  | 696 => 24
  | 2846 => 25
  | 1244 => 26
  | 933 => 27
  | 2384 => 28
  | 3417 => 29
  | 3169 => 30
  | 695 => 31
  | 5839 => 32
  | 2574 => 33
  | 4883 => 34
  | 1935 => 35
  | 841 => 36
  | 3867 => 37
  | 606 => 38
  | 5111 => 39
  | 3364 => 40
  | 2150 => 41
  | 3050 => 42
  | 5812 => 43
  | 5556 => 44
  | 3275 => 45
  | 1392 => 46
  | 173 => 47
  | 1487 => 48
  | 5955 => 49
  | 4142 => 50
  | 5699 => 51
  | 4821 => 52
  | 278 => 53
  | 2202 => 54
  | 6195 => 55
  | 5435 => 56
  | 2664 => 57
  | 5620 => 58
  | 6297 => 59
  | 2602 => 60
  | 5636 => 61
  | 6244 => 62
  | 6219 => 63
  | 5450 => 64
  | 104 => 65
  | 739 => 66
  | 3125 => 67
  | 6487 => 68
  | 1845 => 69
  | 3929 => 70
  | 3509 => 71
  | 3601 => 72
  | 4364 => 73
  | 5009 => 74
  | 610 => 75
  | 5147 => 76
  | 1916 => 77
  | 871 => 78
  | 3855 => 79
  | 2308 => 80
  | 2690 => 81
  | 1946 => 82
  | 3744 => 83
  | 2098 => 84
  | 1412 => 85
  | 177 => 86
  | 1469 => 87
  | 5942 => 88
  | 3282 => 89
  | 699 => 90
  | 5902 => 91
  | 2570 => 92
  | 4863 => 93
  | 3186 => 94
  | 1777 => 95
  | 1606 => 96
  | 4487 => 97
  | 6144 => 98
  | 4775 => 99
  | 5580 => 100
  | 3352 => 101
  | 2166 => 102
  | 3036 => 103
  | 5759 => 104
  | 2948 => 105
  | 5091 => 106
  | 2507 => 107
  | 6394 => 108
  | 391 => 109
  | 3979 => 110
  | 4259 => 111
  | 6406 => 112
  | 1116 => 113
  | 6017 => 114
  | 1400 => 115
  | 172 => 116
  | 1505 => 117
  | 5920 => 118
  | 3303 => 119
  | 4422 => 120
  | 5389 => 121
  | 4094 => 122
  | 2807 => 123
  | 547 => 124
  | 1931 => 125
  | 851 => 126
  | 3833 => 127
  | 604 => 128
  | 5174 => 129
  | 6163 => 130
  | 5490 => 131
  | 2615 => 132
  | 5599 => 133
  | 6284 => 134
  | 757 => 135
  | 3111 => 136
  | 6504 => 137
  | 1828 => 138
  | 106 => 139
  | 3743 => 140
  | 2027 => 141
  | 2286 => 142
  | 2746 => 143
  | 1984 => 144
  | 1313 => 145
  | 1622 => 146
  | 5202 => 147
  | 478 => 148
  | 3685 => 149
  | 821 => 150
  | 3836 => 151
  | 609 => 152
  | 5138 => 153
  | 1878 => 154
  | 5597 => 155
  | 6309 => 156
  | 6187 => 157
  | 5487 => 158
  | 2631 => 159
  | 5316 => 160
  | 1204 => 161
  | 4595 => 162
  | 4620 => 163
  | 999 => 164
  | 102 => 165
  | 748 => 166
  | 3133 => 167
  | 6555 => 168
  | 1840 => 169
  | 2425 => 170
  | 3469 => 171
  | 2867 => 172
  | 1284 => 173
  | 968 => 174
  | 2336 => 175
  | 2714 => 176
  | 1970 => 177
  | 3763 => 178
  | 2096 => 179
  | 2790 => 180
  | 548 => 181
  | 4404 => 182
  | 5424 => 183
  | 4054 => 184
  | 1689 => 185
  | 5261 => 186
  | 481 => 187
  | 3712 => 188
  | 1328 => 189
  | 697 => 190
  | 5884 => 191
  | 2590 => 192
  | 4873 => 193
  | 3233 => 194
  | 1724 => 195
  | 1549 => 196
  | 4502 => 197
  | 6082 => 198
  | 4761 => 199
  | 4185 => 200
  | 5736 => 201
  | 4829 => 202
  | 277 => 203
  | 2193 => 204
  | 2878 => 205
  | 1259 => 206
  | 944 => 207
  | 2410 => 208
  | 3450 => 209
  | 2984 => 210
  | 5063 => 211
  | 2456 => 212
  | 6355 => 213
  | 395 => 214
  | 6325 => 215
  | 387 => 216
  | 2939 => 217
  | 5032 => 218
  | 2477 => 219
  | 900 => 220
  | 2387 => 221
  | 3482 => 222
  | 2857 => 223
  | 1216 => 224
  | 5293 => 225
  | 1167 => 226
  | 4560 => 227
  | 4663 => 228
  | 997 => 229
  | 694 => 230
  | 5857 => 231
  | 2539 => 232
  | 4893 => 233
  | 3183 => 234
  | 3338 => 235
  | 2108 => 236
  | 3015 => 237
  | 5824 => 238
  | 5548 => 239
  | 2446 => 240
  | 6338 => 241
  | 388 => 242
  | 2921 => 243
  | 5067 => 244
  | 179 => 245
  | 1460 => 246
  | 5931 => 247
  | 3313 => 248
  | 1417 => 249
  | 5192 => 250
  | 477 => 251
  | 3676 => 252
  | 1356 => 253
  | 1659 => 254
  | 4601 => 255
  | 4631 => 256
  | 1028 => 257
  | 5322 => 258
  | 1146 => 259
  | 4101 => 260
  | 2824 => 261
  | 545 => 262
  | 4377 => 263
  | 5373 => 264
  | 1317 => 265
  | 1639 => 266
  | 5239 => 267
  | 480 => 268
  | 3703 => 269
  | 4727 => 270
  | 1743 => 271
  | 1574 => 272
  | 4470 => 273
  | 6086 => 274
  | 5746 => 275
  | 4846 => 276
  | 275 => 277
  | 2256 => 278
  | 4208 => 279
  | 766 => 280
  | 3149 => 281
  | 6548 => 282
  | 1823 => 283
  | 107 => 284
  | 925 => 285
  | 2355 => 286
  | 3456 => 287
  | 2901 => 288
  | 1265 => 289
  | 2061 => 290
  | 2330 => 291
  | 2703 => 292
  | 2022 => 293
  | 3730 => 294
  | 911 => 295
  | 2413 => 296
  | 3407 => 297
  | 2880 => 298
  | 1231 => 299
  | 5540 => 300
  | 3390 => 301
  | 2183 => 302
  | 3073 => 303
  | 5818 => 304
  | 5273 => 305
  | 1206 => 306
  | 4567 => 307
  | 4677 => 308
  | 1011 => 309
  | 5476 => 310
  | 2644 => 311
  | 5668 => 312
  | 6250 => 313
  | 6230 => 314
  | 4395 => 315
  | 5365 => 316
  | 4105 => 317
  | 2829 => 318
  | 544 => 319
  | 3534 => 320
  | 3634 => 321
  | 4352 => 322
  | 4944 => 323
  | 3915 => 324
  | 6372 => 325
  | 390 => 326
  | 2966 => 327
  | 5056 => 328
  | 2436 => 329
  | 1749 => 330
  | 1582 => 331
  | 4499 => 332
  | 6128 => 333
  | 4759 => 334
  | 5706 => 335
  | 4841 => 336
  | 273 => 337
  | 2265 => 338
  | 4135 => 339
  | 6001 => 340
  | 4032 => 341
  | 4235 => 342
  | 6409 => 343
  | 1100 => 344
  | 171 => 345
  | 1496 => 346
  | 5993 => 347
  | 3262 => 348
  | 1378 => 349
  | 6464 => 350
  | 1067 => 351
  | 6050 => 352
  | 4026 => 353
  | 4224 => 354
  | 3025 => 355
  | 5784 => 356
  | 5532 => 357
  | 3367 => 358
  | 2131 => 359
  | 5516 => 360
  | 3393 => 361
  | 2137 => 362
  | 3057 => 363
  | 5790 => 364
  | 5716 => 365
  | 4804 => 366
  | 271 => 367
  | 2220 => 368
  | 4155 => 369
  | 6278 => 370
  | 6182 => 371
  | 5464 => 372
  | 2663 => 373
  | 5657 => 374
  | 3513 => 375
  | 3642 => 376
  | 4297 => 377
  | 4977 => 378
  | 3950 => 379
  | 4309 => 380
  | 4961 => 381
  | 3952 => 382
  | 3488 => 383
  | 3609 => 384
  | 4473 => 385
  | 6148 => 386
  | 4738 => 387
  | 1718 => 388
  | 1541 => 389
  | 2170 => 390
  | 3002 => 391
  | 5796 => 392
  | 5524 => 393
  | 3341 => 394
  | 542 => 395
  | 4431 => 396
  | 5358 => 397
  | 4115 => 398
  | 2768 => 399
  | 1523 => 400
  | 5927 => 401
  | 3296 => 402
  | 1434 => 403
  | 174 => 404
  | 6206 => 405
  | 5461 => 406
  | 2598 => 407
  | 5643 => 408
  | 6303 => 409
  | 1803 => 410
  | 100 => 411
  | 784 => 412
  | 3153 => 413
  | 6538 => 414
  | 3541 => 415
  | 3585 => 416
  | 4312 => 417
  | 4996 => 418
  | 3963 => 419
  | 2621 => 420
  | 5631 => 421
  | 6272 => 422
  | 6171 => 423
  | 5438 => 424
  | 1040 => 425
  | 5306 => 426
  | 1160 => 427
  | 4573 => 428
  | 4688 => 429
  | 775 => 430
  | 3103 => 431
  | 6508 => 432
  | 1815 => 433
  | 105 => 434
  | 1478 => 435
  | 5977 => 436
  | 3245 => 437
  | 1422 => 438
  | 178 => 439
  | 5354 => 440
  | 4122 => 441
  | 2785 => 442
  | 546 => 443
  | 4413 => 444
  | 3694 => 445
  | 1348 => 446
  | 1699 => 447
  | 5197 => 448
  | 479 => 449
  | 5610 => 450
  | 6256 => 451
  | 6211 => 452
  | 5502 => 453
  | 2650 => 454
  | 4525 => 455
  | 6134 => 456
  | 4701 => 457
  | 1728 => 458
  | 1590 => 459
  | 5019 => 460
  | 3892 => 461
  | 3519 => 462
  | 3626 => 463
  | 4323 => 464
  | 1998 => 465
  | 3792 => 466
  | 2075 => 467
  | 2302 => 468
  | 2679 => 469
  | 949 => 470
  | 2370 => 471
  | 3421 => 472
  | 2890 => 473
  | 1290 => 474
  | 5335 => 475
  | 1193 => 476
  | 4539 => 477
  | 4644 => 478
  | 1023 => 479
  | 2342 => 480
  | 2722 => 481
  | 1996 => 482
  | 3805 => 483
  | 2038 => 484
  | 1629 => 485
  | 5222 => 486
  | 485 => 487
  | 3667 => 488
  | 1297 => 489
  | 5911 => 490
  | 2524 => 491
  | 4934 => 492
  | 3208 => 493
  | 700 => 494
  | 5970 => 495
  | 3252 => 496
  | 1442 => 497
  | 176 => 498
  | 1514 => 499
  | 2467 => 500
  | 6389 => 501
  | 392 => 502
  | 2957 => 503
  | 5048 => 504
  | 4177 => 505
  | 5695 => 506
  | 4807 => 507
  | 276 => 508
  | 2211 => 509
  | 6461 => 510
  | 1083 => 511
  | 6072 => 512
  | 3973 => 513
  | 4248 => 514
  | 5893 => 515
  | 2559 => 516
  | 4903 => 517
  | 3203 => 518
  | 701 => 519
  | 3013 => 520
  | 5771 => 521
  | 5572 => 522
  | 3326 => 523
  | 2151 => 524
  | 3908 => 525
  | 3547 => 526
  | 3569 => 527
  | 4338 => 528
  | 4957 => 529
  | 3436 => 530
  | 2841 => 531
  | 1269 => 532
  | 957 => 533
  | 2399 => 534
  | 4386 => 535
  | 5411 => 536
  | 4064 => 537
  | 2810 => 538
  | 543 => 539
  | 828 => 540
  | 3880 => 541
  | 607 => 542
  | 5120 => 543
  | 1865 => 544
  | 3062 => 545
  | 5765 => 546
  | 5564 => 547
  | 3378 => 548
  | 2118 => 549
  | 4001 => 550
  | 4281 => 551
  | 6476 => 552
  | 1129 => 553
  | 6061 => 554
  | 4639 => 555
  | 973 => 556
  | 5274 => 557
  | 1172 => 558
  | 4616 => 559
  | 5404 => 560
  | 4071 => 561
  | 2773 => 562
  | 541 => 563
  | 4449 => 564
  | 5253 => 565
  | 482 => 566
  | 3721 => 567
  | 1363 => 568
  | 1652 => 569
  | 4166 => 570
  | 5685 => 571
  | 4790 => 572
  | 272 => 573
  | 2229 => 574
  | 6040 => 575
  | 3994 => 576
  | 4240 => 577
  | 6432 => 578
  | 1077 => 579
  | 101 => 580
  | 793 => 581
  | 3083 => 582
  | 6525 => 583
  | 1798 => 584
  | 2010 => 585
  | 3776 => 586
  | 2059 => 587
  | 2274 => 588
  | 2727 => 589
  | 5678 => 590
  | 4851 => 591
  | 274 => 592
  | 2247 => 593
  | 4170 => 594
  | 393 => 595
  | 2993 => 596
  | 5098 => 597
  | 2497 => 598
  | 6350 => 599
  | 1756 => 600
  | 1614 => 601
  | 4513 => 602
  | 6096 => 603
  | 4717 => 604
  | 1771 => 605
  | 1598 => 606
  | 4458 => 607
  | 6102 => 608
  | 4749 => 609
  | 1924 => 610
  | 858 => 611
  | 3850 => 612
  | 611 => 613
  | 5156 => 614
  | 888 => 615
  | 3811 => 616
  | 603 => 617
  | 5165 => 618
  | 1893 => 619
  | 2314 => 620
  | 2698 => 621
  | 1972 => 622
  | 3759 => 623
  | 2049 => 624
  | 6369 => 625
  | 394 => 626
  | 2975 => 627
  | 5025 => 628
  | 2457 => 629
  | 4588 => 630
  | 4696 => 631
  | 985 => 632
  | 5339 => 633
  | 1183 => 634
  | 484 => 635
  | 3658 => 636
  | 1370 => 637
  | 1669 => 638
  | 5236 => 639
  | 1557 => 640
  | 4528 => 641
  | 6115 => 642
  | 4715 => 643
  | 1703 => 644
  | 2082 => 645
  | 2280 => 646
  | 2738 => 647
  | 1958 => 648
  | 3782 => 649
  | 608 => 650
  | 5129 => 651
  | 1900 => 652
  | 881 => 653
  | 3875 => 654
  | 1682 => 655
  | 5214 => 656
  | 483 => 657
  | 3649 => 658
  | 1332 => 659
  | 3164 => 660
  | 693 => 661
  | 5848 => 662
  | 2531 => 663
  | 4924 => 664
  | 698 => 665
  | 5866 => 666
  | 2517 => 667
  | 4914 => 668
  | 3225 => 669
  | 389 => 670
  | 2930 => 671
  | 5078 => 672
  | 2487 => 673
  | 6330 => 674
  | 5287 => 675
  | 1135 => 676
  | 4545 => 677
  | 4655 => 678
  | 1052 => 679
  | 4273 => 680
  | 6447 => 681
  | 1096 => 682
  | 6038 => 683
  | 4022 => 684
  | 4047 => 685
  | 4216 => 686
  | 6435 => 687
  | 1115 => 688
  | 6024 => 689
  | 2238 => 690
  | 4201 => 691
  | 5729 => 692
  | 4782 => 693
  | 270 => 694
  | 3292 => 695
  | 1456 => 696
  | 175 => 697
  | 1532 => 698
  | 5962 => 699
  | 3562 => 700
  | 3577 => 701
  | 4367 => 702
  | 4990 => 703
  | 3940 => 704
  | 99 => 705
  | 802 => 706
  | 3118 => 707
  | 6497 => 708
  | 1784 => 709
  | 5396 => 710
  | 4084 => 711
  | 2760 => 712
  | 540 => 713
  | 4440 => 714
  | 6421 => 715
  | 1054 => 716
  | 6003 => 717
  | 4007 => 718
  | 4292 => 719
  | _ => 0

private theorem a6SLDecode_code_b0 (r : Fin 60) :
    let n : Fin 720 := ⟨r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b1 (r : Fin 60) :
    let n : Fin 720 := ⟨60 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b2 (r : Fin 60) :
    let n : Fin 720 := ⟨120 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b3 (r : Fin 60) :
    let n : Fin 720 := ⟨180 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b4 (r : Fin 60) :
    let n : Fin 720 := ⟨240 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b5 (r : Fin 60) :
    let n : Fin 720 := ⟨300 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b6 (r : Fin 60) :
    let n : Fin 720 := ⟨360 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b7 (r : Fin 60) :
    let n : Fin 720 := ⟨420 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b8 (r : Fin 60) :
    let n : Fin 720 := ⟨480 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b9 (r : Fin 60) :
    let n : Fin 720 := ⟨540 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b10 (r : Fin 60) :
    let n : Fin 720 := ⟨600 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code_b11 (r : Fin 60) :
    let n : Fin 720 := ⟨660 + r.val, by omega⟩
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecode_code (n : Fin 720) :
    a6SLDecode (a6SLCode (a6SLNormalForm (a6SLNormalPair n))) = n := by
  by_cases h0 : n.val < 60
  · let r : Fin 60 := ⟨n.val - 0, by omega⟩
    have hn : (⟨0 + r.val, by omega⟩ : Fin 720) = n := by
      apply Fin.ext
      simp [r]
    rw [← hn]
    simpa only [zero_add] using a6SLDecode_code_b0 r
  · by_cases h1 : n.val < 120
    · let r : Fin 60 := ⟨n.val - 60, by omega⟩
      have hn : (⟨60 + r.val, by omega⟩ : Fin 720) = n := by
        apply Fin.ext
        simp [r]
        omega
      rw [← hn]
      exact a6SLDecode_code_b1 r
    · by_cases h2 : n.val < 180
      · let r : Fin 60 := ⟨n.val - 120, by omega⟩
        have hn : (⟨120 + r.val, by omega⟩ : Fin 720) = n := by
          apply Fin.ext
          simp [r]
          omega
        rw [← hn]
        exact a6SLDecode_code_b2 r
      · by_cases h3 : n.val < 240
        · let r : Fin 60 := ⟨n.val - 180, by omega⟩
          have hn : (⟨180 + r.val, by omega⟩ : Fin 720) = n := by
            apply Fin.ext
            simp [r]
            omega
          rw [← hn]
          exact a6SLDecode_code_b3 r
        · by_cases h4 : n.val < 300
          · let r : Fin 60 := ⟨n.val - 240, by omega⟩
            have hn : (⟨240 + r.val, by omega⟩ : Fin 720) = n := by
              apply Fin.ext
              simp [r]
              omega
            rw [← hn]
            exact a6SLDecode_code_b4 r
          · by_cases h5 : n.val < 360
            · let r : Fin 60 := ⟨n.val - 300, by omega⟩
              have hn : (⟨300 + r.val, by omega⟩ : Fin 720) = n := by
                apply Fin.ext
                simp [r]
                omega
              rw [← hn]
              exact a6SLDecode_code_b5 r
            · by_cases h6 : n.val < 420
              · let r : Fin 60 := ⟨n.val - 360, by omega⟩
                have hn : (⟨360 + r.val, by omega⟩ : Fin 720) = n := by
                  apply Fin.ext
                  simp [r]
                  omega
                rw [← hn]
                exact a6SLDecode_code_b6 r
              · by_cases h7 : n.val < 480
                · let r : Fin 60 := ⟨n.val - 420, by omega⟩
                  have hn : (⟨420 + r.val, by omega⟩ : Fin 720) = n := by
                    apply Fin.ext
                    simp [r]
                    omega
                  rw [← hn]
                  exact a6SLDecode_code_b7 r
                · by_cases h8 : n.val < 540
                  · let r : Fin 60 := ⟨n.val - 480, by omega⟩
                    have hn : (⟨480 + r.val, by omega⟩ : Fin 720) = n := by
                      apply Fin.ext
                      simp [r]
                      omega
                    rw [← hn]
                    exact a6SLDecode_code_b8 r
                  · by_cases h9 : n.val < 600
                    · let r : Fin 60 := ⟨n.val - 540, by omega⟩
                      have hn : (⟨540 + r.val, by omega⟩ : Fin 720) = n := by
                        apply Fin.ext
                        simp [r]
                        omega
                      rw [← hn]
                      exact a6SLDecode_code_b9 r
                    · by_cases h10 : n.val < 660
                      · let r : Fin 60 := ⟨n.val - 600, by omega⟩
                        have hn : (⟨600 + r.val, by omega⟩ : Fin 720) = n := by
                          apply Fin.ext
                          simp [r]
                          omega
                        rw [← hn]
                        exact a6SLDecode_code_b10 r
                      · let r : Fin 60 := ⟨n.val - 660, by omega⟩
                        have hn : (⟨660 + r.val, by omega⟩ : Fin 720) = n := by
                          apply Fin.ext
                          simp [r]
                          omega
                        rw [← hn]
                        exact a6SLDecode_code_b11 r

private theorem a6SLDecode_normalForm (x : Fin 144 × Fin 5) :
    a6SLDecode (a6SLCode (a6SLNormalForm x)) = a6SLNormalIndex x := by
  rw [← a6SLNormalPair_index x]
  simpa only [a6SLNormalIndex_pair] using a6SLDecode_code (a6SLNormalIndex x)

private theorem a6SLNormalForm_injective : Function.Injective a6SLNormalForm := by
  intro x y h
  apply a6SLNormalIndex_injective
  rw [← a6SLDecode_normalForm x, ← a6SLDecode_normalForm y, h]

private theorem a6SLNormalForm_bijective : Function.Bijective a6SLNormalForm := by
  apply (Nat.bijective_iff_injective_and_card a6SLNormalForm).2
  refine ⟨a6SLNormalForm_injective, ?_⟩
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fin, a6SL_card]

private noncomputable def a6SLNormalEquiv : (Fin 144 × Fin 5) ≃ A6SL :=
  Equiv.ofBijective a6SLNormalForm a6SLNormalForm_bijective

@[reducible] private def a6SLCosetRep (r : Fin 144) : A6SL ⧸ a6SLStabilizer :=
  a6SLRep r

private theorem a6SLCosetRep_injective : Function.Injective a6SLCosetRep := by
  intro r s h
  have hz : (a6SLRep r)⁻¹ * a6SLRep s ∈ a6SLStabilizer := by
    rw [← QuotientGroup.leftRel_apply]
    exact Quotient.eq.mp h
  let zH : a6SLStabilizer := ⟨(a6SLRep r)⁻¹ * a6SLRep s, hz⟩
  let k0 : Fin (orderOf a6SLGen1) :=
    (finEquivZPowers (isOfFinOrder_of_finite a6SLGen1)).symm zH
  let k : Fin 5 := Fin.cast a6SLGen1_order k0
  have hzpow : a6SLGen1 ^ k.val = (a6SLRep r)⁻¹ * a6SLRep s := by
    simpa [k, k0, zH] using
      pow_finEquivZPowers_symm_apply (isOfFinOrder_of_finite a6SLGen1) zH
  have hnf : a6SLNormalForm (r, k) = a6SLNormalForm (s, 0) := by
    change a6SLRep r * a6SLGen1 ^ k.val = a6SLRep s * a6SLGen1 ^ (0 : Fin 5).val
    rw [hzpow]
    simp only [Fin.val_zero, pow_zero, mul_one]
    simp
  exact congrArg Prod.fst (a6SLNormalForm_injective hnf)

private theorem a6SLCoset_card : Nat.card (A6SL ⧸ a6SLStabilizer) = 144 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup a6SLStabilizer
  rw [a6SL_card, a6SLStabilizer_card] at h
  omega

private theorem a6SLCosetRep_bijective : Function.Bijective a6SLCosetRep := by
  apply (Nat.bijective_iff_injective_and_card a6SLCosetRep).2
  exact ⟨a6SLCosetRep_injective, by rw [Nat.card_fin, a6SLCoset_card]⟩

private noncomputable def a6SLCosetEquiv : Fin 144 ≃ (A6SL ⧸ a6SLStabilizer) :=
  Equiv.ofBijective a6SLCosetRep a6SLCosetRep_bijective

@[reducible] private def a6SLDecodedFirst (g : A6SL) : Fin 144 :=
  ⟨(a6SLDecode (a6SLCode g)).val / 5, by omega⟩

private theorem a6SLDecodedFirst_normalForm (x : Fin 144 × Fin 5) :
    a6SLDecodedFirst (a6SLNormalForm x) = x.1 := by
  apply Fin.ext
  have h := congrArg Fin.val (a6SLDecode_normalForm x)
  change (a6SLDecode (a6SLCode (a6SLNormalForm x))).val / 5 = x.1.val
  change (a6SLDecode (a6SLCode (a6SLNormalForm x))).val = x.1.val * 5 + x.2.val at h
  omega

private theorem a6SLDecodedFirst_gen1 (r : Fin 144) :
    a6SLDecodedFirst (a6SLGen1 * a6SLRep r) = a6DoubleCoverGen1 r := by
  fin_cases r <;> decide +kernel

private theorem a6SLDecodedFirst_gen2 (r : Fin 144) :
    a6SLDecodedFirst (a6SLGen2 * a6SLRep r) = a6DoubleCoverGen2 r := by
  fin_cases r <;> decide +kernel

private theorem a6SLCoset_normalForm (x : Fin 144 × Fin 5) :
    ((a6SLNormalForm x : A6SL) : A6SL ⧸ a6SLStabilizer) =
      ((a6SLRep x.1 : A6SL) : A6SL ⧸ a6SLStabilizer) := by
  apply Quotient.eq.2
  rw [QuotientGroup.leftRel_apply]
  change (a6SLNormalForm x)⁻¹ * a6SLRep x.1 ∈ a6SLStabilizer
  simpa [a6SLNormalForm] using
    a6SLStabilizer.inv_mem
      (a6SLStabilizer.pow_mem (Subgroup.mem_zpowers a6SLGen1) x.2.val)

private theorem a6SLCoset_action_gen1 (r : Fin 144) :
    a6SLGen1 • a6SLCosetEquiv r = a6SLCosetEquiv (a6DoubleCoverGen1 r) := by
  change ((a6SLGen1 * a6SLRep r : A6SL) : A6SL ⧸ a6SLStabilizer) =
    ((a6SLRep (a6DoubleCoverGen1 r) : A6SL) : A6SL ⧸ a6SLStabilizer)
  let x := a6SLNormalEquiv.symm (a6SLGen1 * a6SLRep r)
  have hx : a6SLNormalForm x = a6SLGen1 * a6SLRep r :=
    a6SLNormalEquiv.apply_symm_apply (a6SLGen1 * a6SLRep r)
  have hfirst : x.1 = a6DoubleCoverGen1 r := by
    rw [← a6SLDecodedFirst_normalForm x, hx]
    exact a6SLDecodedFirst_gen1 r
  calc
    ((a6SLGen1 * a6SLRep r : A6SL) : A6SL ⧸ a6SLStabilizer) =
        ((a6SLNormalForm x : A6SL) : A6SL ⧸ a6SLStabilizer) :=
      congrArg (fun g : A6SL => (g : A6SL ⧸ a6SLStabilizer)) hx.symm
    _ = ((a6SLRep x.1 : A6SL) : A6SL ⧸ a6SLStabilizer) := a6SLCoset_normalForm x
    _ = ((a6SLRep (a6DoubleCoverGen1 r) : A6SL) : A6SL ⧸ a6SLStabilizer) := by rw [hfirst]

private theorem a6SLCoset_action_gen2 (r : Fin 144) :
    a6SLGen2 • a6SLCosetEquiv r = a6SLCosetEquiv (a6DoubleCoverGen2 r) := by
  change ((a6SLGen2 * a6SLRep r : A6SL) : A6SL ⧸ a6SLStabilizer) =
    ((a6SLRep (a6DoubleCoverGen2 r) : A6SL) : A6SL ⧸ a6SLStabilizer)
  let x := a6SLNormalEquiv.symm (a6SLGen2 * a6SLRep r)
  have hx : a6SLNormalForm x = a6SLGen2 * a6SLRep r :=
    a6SLNormalEquiv.apply_symm_apply (a6SLGen2 * a6SLRep r)
  have hfirst : x.1 = a6DoubleCoverGen2 r := by
    rw [← a6SLDecodedFirst_normalForm x, hx]
    exact a6SLDecodedFirst_gen2 r
  calc
    ((a6SLGen2 * a6SLRep r : A6SL) : A6SL ⧸ a6SLStabilizer) =
        ((a6SLNormalForm x : A6SL) : A6SL ⧸ a6SLStabilizer) :=
      congrArg (fun g : A6SL => (g : A6SL ⧸ a6SLStabilizer)) hx.symm
    _ = ((a6SLRep x.1 : A6SL) : A6SL ⧸ a6SLStabilizer) := a6SLCoset_normalForm x
    _ = ((a6SLRep (a6DoubleCoverGen2 r) : A6SL) : A6SL ⧸ a6SLStabilizer) := by rw [hfirst]

private noncomputable def a6SLPermHom : A6SL →* Perm144 :=
  a6SLCosetEquiv.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom A6SL (A6SL ⧸ a6SLStabilizer))

private theorem a6SLPermHom_gen1 : a6SLPermHom a6SLGen1 = a6DoubleCoverGen1 := by
  apply Equiv.ext
  intro r
  change a6SLCosetEquiv.symm (a6SLGen1 • a6SLCosetEquiv r) = a6DoubleCoverGen1 r
  apply a6SLCosetEquiv.injective
  rw [a6SLCosetEquiv.apply_symm_apply]
  exact a6SLCoset_action_gen1 r

private theorem a6SLPermHom_gen2 : a6SLPermHom a6SLGen2 = a6DoubleCoverGen2 := by
  apply Equiv.ext
  intro r
  change a6SLCosetEquiv.symm (a6SLGen2 • a6SLCosetEquiv r) = a6DoubleCoverGen2 r
  apply a6SLCosetEquiv.injective
  rw [a6SLCosetEquiv.apply_symm_apply]
  exact a6SLCoset_action_gen2 r

@[expose] public def a6DoubleCoverPermutationSubgroup : Subgroup Perm144 :=
  Subgroup.closure {a6DoubleCoverGen1, a6DoubleCoverGen2}

private theorem a6DoubleCoverPermutationSubgroup_le_a6SL_range :
    a6DoubleCoverPermutationSubgroup ≤ a6SLPermHom.range := by
  rw [a6DoubleCoverPermutationSubgroup, Subgroup.closure_le]
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact ⟨a6SLGen1, a6SLPermHom_gen1⟩
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact ⟨a6SLGen2, a6SLPermHom_gen2⟩

public theorem a6DoubleCoverPermutationSubgroup_card_le :
    Nat.card a6DoubleCoverPermutationSubgroup ≤ 720 := by
  calc
    Nat.card a6DoubleCoverPermutationSubgroup ≤ Nat.card a6SLPermHom.range :=
      Subgroup.card_le_of_le a6DoubleCoverPermutationSubgroup_le_a6SL_range
    _ ≤ Nat.card A6SL := Nat.card_le_card_of_surjective
      a6SLPermHom.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    _ = 720 := a6SL_card

private def a6SLGenerated : Subgroup A6SL :=
  Subgroup.closure {a6SLGen1, a6SLGen2}

private theorem a6SLGenerated_evalWord_mem (w : List (Fin 4)) :
    Theory.GroupTheory.evalWord a6SLChainGen w ∈ a6SLGenerated := by
  induction w with
  | nil => exact a6SLGenerated.one_mem
  | cons i w ih =>
      apply a6SLGenerated.mul_mem _ ih
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact a6SLGenerated.inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · exact a6SLGenerated.inv_mem
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem a6SLGenerated_rep_mem (r : Fin 144) :
    a6SLRep r ∈ a6SLGenerated :=
  a6SLGenerated_evalWord_mem (a6ChainRepWord0 r)

private theorem a6SLGenerated_normalForm_mem (x : Fin 144 × Fin 5) :
    a6SLNormalForm x ∈ a6SLGenerated := by
  exact a6SLGenerated.mul_mem (a6SLGenerated_rep_mem x.1)
    (a6SLGenerated.pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) x.2.val)

private theorem a6SLGenerated_eq_top : a6SLGenerated = ⊤ := by
  apply top_unique
  intro g hg
  let x := a6SLNormalEquiv.symm g
  rw [← a6SLNormalEquiv.apply_symm_apply g]
  exact a6SLGenerated_normalForm_mem x

private theorem a6SLPermHom_range_le_a6DoubleCoverPermutationSubgroup :
    a6SLPermHom.range ≤ a6DoubleCoverPermutationSubgroup := by
  intro y hy
  rcases hy with ⟨(g : A6SL), rfl⟩
  have hg : g ∈ a6SLGenerated := by
    simp [a6SLGenerated_eq_top]
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · rw [a6SLPermHom_gen1]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hg
        subst g
        rw [a6SLPermHom_gen2]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  | one => simp
  | mul x y hx hy ihx ihy => simpa [map_mul] using
      a6DoubleCoverPermutationSubgroup.mul_mem ihx ihy
  | inv x hx ih => simpa [map_inv] using a6DoubleCoverPermutationSubgroup.inv_mem ih

private theorem a6DoubleCoverGen1_order : orderOf a6DoubleCoverGen1 = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime (by
    ext x
    decide +revert +kernel) (by
    intro h
    have hx := congrArg (fun p : Perm144 => p 1) h
    exact (by decide : a6DoubleCoverGen1 1 ≠ (1 : Fin 144)) hx)

private theorem a6DoubleCoverGen1_fixed_one_iff (nf : Fin 5)
    (h : (a6DoubleCoverGen1 ^ (nf.val : ℤ)) 1 = (1 : Fin 144)) : nf = 0 := by
  fin_cases nf <;> first | rfl | (exfalso; revert h; decide)

private theorem a6SLAction_faithful :
    FaithfulSMul A6SL (A6SL ⧸ a6SLStabilizer) := by
  apply faithfulSMul_iff.mpr
  intro g hfix
  have hmem : g ∈ a6SLStabilizer := by
    have hq : ((g : A6SL) : A6SL ⧸ a6SLStabilizer) =
        ((1 : A6SL) : A6SL ⧸ a6SLStabilizer) := by
      simpa [smul_eq_mul] using hfix ((1 : A6SL) : A6SL ⧸ a6SLStabilizer)
    have hraw := QuotientGroup.eq.mp hq
    have hginv : g⁻¹ ∈ a6SLStabilizer := by simpa using hraw
    simpa using a6SLStabilizer.inv_mem hginv
  rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨n, hn⟩
  have hperm : a6SLPermHom g 1 = (1 : Fin 144) := by
    change a6SLCosetEquiv.symm (g • a6SLCosetEquiv 1) = 1
    rw [hfix]
    exact a6SLCosetEquiv.symm_apply_apply _
  rw [← hn, map_zpow, a6SLPermHom_gen1] at hperm
  have hp := zpow_mod_orderOf a6DoubleCoverGen1 n
  rw [a6DoubleCoverGen1_order] at hp
  have hperm_mod :
      (a6DoubleCoverGen1 ^ (n % (5 : ℤ))) 1 = (1 : Fin 144) := by
    rw [← hp] at hperm
    exact hperm
  have hn_nonneg : 0 ≤ n % (5 : ℤ) := Int.emod_nonneg _ (by norm_num)
  let nf : Fin 5 := ⟨(n % (5 : ℤ)).toNat, (Int.toNat_lt hn_nonneg).mpr (by
    simpa using (Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 5)))⟩
  have hperm_mod' : (a6DoubleCoverGen1 ^ (nf.val : ℤ)) 1 = (1 : Fin 144) := by
    simpa [nf, Int.toNat_of_nonneg hn_nonneg] using hperm_mod
  have hnf : nf = 0 := a6DoubleCoverGen1_fixed_one_iff nf hperm_mod'
  have hnmod0 : n % (5 : ℤ) = 0 := by
    have hzero : (n % (5 : ℤ)).toNat = 0 := by
      simpa [nf] using congrArg Fin.val hnf
    have hle : n % (5 : ℤ) ≤ 0 := Int.toNat_eq_zero.mp hzero
    omega
  have hngen : g = 1 := by
    have hp := zpow_mod_orderOf a6SLGen1 n
    rw [a6SLGen1_order] at hp
    rw [← hn, ← hp]
    simp [hnmod0]
  exact hngen

private theorem a6SLPermHom_injective : Function.Injective a6SLPermHom := by
  intro g h hgh
  have hact : MulAction.toPermHom A6SL (A6SL ⧸ a6SLStabilizer) g =
      MulAction.toPermHom A6SL (A6SL ⧸ a6SLStabilizer) h := by
    apply a6SLCosetEquiv.symm.permCongrHom.injective
    simpa [a6SLPermHom] using hgh
  have hfix : ∀ a : A6SL ⧸ a6SLStabilizer, g • a = h • a := by
    intro a
    have ha := congrArg (fun p : Equiv.Perm (A6SL ⧸ a6SLStabilizer) => p a) hact
    simpa [MulAction.toPermHom] using ha
  apply eq_of_mul_inv_eq_one
  apply (faithfulSMul_iff.mp a6SLAction_faithful)
  intro a
  rw [mul_smul]
  rw [hfix]
  simp

public theorem a6DoubleCoverPermutationSubgroup_card_ge :
    720 ≤ Nat.card a6DoubleCoverPermutationSubgroup := by
  have hinj : Function.Injective a6SLPermHom.rangeRestrict := by
    intro g h hgh
    apply a6SLPermHom_injective
    exact congrArg Subtype.val hgh
  calc
    720 = Nat.card A6SL := a6SL_card.symm
    _ ≤ Nat.card a6SLPermHom.range := Nat.card_le_card_of_injective
      a6SLPermHom.rangeRestrict hinj
    _ ≤ Nat.card a6DoubleCoverPermutationSubgroup :=
      Subgroup.card_le_of_le a6SLPermHom_range_le_a6DoubleCoverPermutationSubgroup

public theorem a6DoubleCoverPermutationSubgroup_card :
    Nat.card a6DoubleCoverPermutationSubgroup = 720 := by
  exact Nat.le_antisymm a6DoubleCoverPermutationSubgroup_card_le
    a6DoubleCoverPermutationSubgroup_card_ge

end GLS3.Chapter5

/- END Theory.A6DoubleCoverOrderData -/

/- BEGIN Theory.A6DoubleCoverOrderStep0Early -/
namespace GLS3.Chapter5

set_option Elab.async false in
public theorem a6ChainStep0_i0_b0 (r : Fin 4) :
    let s : Fin 144 := ⟨0 + r.val, by omega⟩
    a6ChainGen0 0 * a6ChainRep0 s =
      a6ChainRep0 (a6ChainGen0 0 s) *
        evalWord a6ChainGen1 (a6ChainFactor0 0 s) := by
  fin_cases r <;> rfl

end GLS3.Chapter5
/- END Theory.A6DoubleCoverOrderStep0Early -/
