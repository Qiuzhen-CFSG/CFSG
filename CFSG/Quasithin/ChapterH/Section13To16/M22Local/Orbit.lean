module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers

/-!
# The M22 source pair orbit and the outer-stabilizer diagnostic

The literal ten-dimensional cocode has the source 22-vector nonzero orbit
under both native M22 and its actual degree-24 setwise-pair extension. The
extension is identified with Aut(M22), compatibly with the original embedding.
Both vector stabilizers generate the entire module by displacements. Their
orders distinguish the inner and outer readings of the printed H.15.1 claim.

The compatible stabilizer identifications use the actual PSL(3,4) carrier
and its extension by field Frobenius. The stronger displacement conclusions
retain the actual solvable residual of each vector stabilizer.

Source: Aschbacher--Smith, H.13.1, H.15.1 and 8.1.1, printed pp.395,398,712.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local
open MathieuCode Representation.BinaryOffender
open Sporadic.Mathieu

/-- The full source extension is the actual automorphism group. -/
def pairGroupEquivAut : m22PairStabilizer ≃* MulAut M22 := m22PairStabilizerEquivAut

theorem pairGroupEquivAut_inner (g : M22) :
    pairGroupEquivAut (m22ToPairStabilizer g) = MulAut.conj g :=
  m22PairStabilizerEquivAut_inner g

/-- The source O₂ consists of 22 nonzero vectors and is a single orbit. -/
theorem pair_orbit (i : Fin 22) :
    Nat.card m22WeightTwoFamily = 22 ∧
    (∀ v ∈ m22WeightTwoFamily, v ≠ 0) ∧
    m22WeightTwoFamily = {v | ∃ g : M22, m22CocodeRepresentation g (m22WeightTwoVector i) = v} ∧
    m22WeightTwoFamily = {v | ∃ g : m22PairStabilizer,
      m22OuterCocodeRepresentation g (m22WeightTwoVector i) = v} :=
  ⟨m22WeightTwoFamily_card, fun _ h => m22WeightTwoFamily_nonzero h,
    m22WeightTwoFamily_orbit i, m22WeightTwoFamily_outer_orbit i⟩

/-- H.15.1(2) under the native M22 action. -/
theorem pair_commutator {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    subspaceCommutator m22CocodeRepresentation ⊤ (m22CocodeStabilizer m22CocodeRepresentation v) = ⊤ := by
  obtain ⟨i, rfl⟩ := hv
  exact m22WeightTwoVector_commutator_eq_top i

/-- H.15.1(2) for the actual full setwise-pair extension. -/
theorem pair_outer_commutator {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    subspaceCommutator m22OuterCocodeRepresentation ⊤
      (m22CocodeStabilizer m22OuterCocodeRepresentation v) = ⊤ := by
  obtain ⟨i, rfl⟩ := hv
  exact m22WeightTwoVector_outer_commutator_eq_top i

/-- The literal outer L3(4) clause of H.15.1 conflicts with the actual action.
The inner stabilizer is the one used in 8.1.1. -/
theorem pair_stabilizer_diagnostic {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    Nat.card (m22CocodeStabilizer m22CocodeRepresentation v) = 20160 ∧
    Nat.card (m22CocodeStabilizer m22OuterCocodeRepresentation v) = 40320 ∧
    ¬ Nonempty (m22CocodeStabilizer m22OuterCocodeRepresentation v ≃* Matrix.PSL3Four.PSL) := by
  obtain ⟨i, rfl⟩ := hv
  exact ⟨m22WeightTwoVector_stabilizer_card i, m22WeightTwoVector_outer_stabilizer_card i,
    m22WeightTwoVector_outer_not_equiv_PSL i⟩

/-- The actual inner stabilizer required by 8.1.1 is L3(4). -/
theorem pair_stabilizer {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    Nonempty (m22CocodeStabilizer m22CocodeRepresentation v ≃* Matrix.PSL3Four.PSL) := by
  obtain ⟨i, rfl⟩ := hv
  exact ⟨m22WeightTwoVector_stabilizer_equiv i⟩

/-- The full outer stabilizer is the genuine field extension of L3(4). -/
theorem pair_outer_stabilizer {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    Nonempty (m22CocodeStabilizer m22OuterCocodeRepresentation v ≃* Matrix.PSL3Four.FieldExtension) := by
  obtain ⟨i, rfl⟩ := hv
  exact ⟨m22WeightTwoVector_outer_stabilizer_equiv i⟩

/-- The native perfect-residual action required in 8.1.1. -/
theorem pair_residual_commutator {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    subspaceCommutator m22CocodeRepresentation ⊤
      ((Subgroup.solvableResidual (m22CocodeStabilizer m22CocodeRepresentation v)).map
        (m22CocodeStabilizer m22CocodeRepresentation v).subtype) = ⊤ := by
  obtain ⟨i, rfl⟩ := hv
  exact m22WeightTwoVector_residual_commutator i

/-- The analogous statement for the actual full outer stabilizer's residual. -/
theorem pair_outer_residual_commutator {v : M22Cocode} (hv : v ∈ m22WeightTwoFamily) :
    subspaceCommutator m22OuterCocodeRepresentation ⊤
      ((Subgroup.solvableResidual (m22CocodeStabilizer m22OuterCocodeRepresentation v)).map
        (m22CocodeStabilizer m22OuterCocodeRepresentation v).subtype) = ⊤ := by
  obtain ⟨i, rfl⟩ := hv
  exact m22WeightTwoVector_outer_residual_commutator i

end CFSG.Quasithin.ChapterH.Section13To16.M22Local
