module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.Stabilizer
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.StabilizerCommutativity
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.Perfectness
public import Theory.AtlasPort.GroupTheory.G2IwasawaStabilizer
public import Theory.AlgebraicGroup.Dimension.Finite

/-!
# Root extraction from positive-dimensional normal Spin subgroups

The concrete first simple root fixes a singular line. Its normal closure
inside the line stabilizer is normal there and normally generates Spin.
The action on singular lines is faithful and primitive, and this relative
root closure is abelian. Iwasawa's argument and the already proved
perfectness force every nontrivial normal subgroup to equal Spin. A closed
subgroup of nonzero dimension is nontrivial, so it then contains the first
root element with parameter one.

The conditional reductions are retained, and `exists_rootPoint_mem` discharges
all three geometric hypotheses using the concrete singular-line action and
Siegel subgroup calculations. This supplies the root-extraction input to the
separate algebraic-simplicity assembly. No abstract simplicity premise or
algebraic inverse to the Spin cover is used.

Source: GLS3, 1.7.1 and the type-D case of 1.10.1(b),
`refs/KGroup/GLS3/Chapter1.tex`. The imported Iwasawa argument is the existing
attributed ATLAS port; see its module header and LICENSES/ATLAS.txt.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Iwasawa reduction for the actual Spin carrier, with the geometric inputs explicit. -/
theorem normal_eq_top_of_singularLine_geometry
    (hfaith : FaithfulSMul (Points k) (SingularLines k))
    (hprimitive : MulAction.IsPreprimitive (Points k) (SingularLines k))
    (hcomm : IsMulCommutative (lineRootClosure k))
    (N : Subgroup (Points k)) (hN : N.Normal) (hne : N ≠ ⊥) : N = ⊤ := by
  let := hfaith
  let := hprimitive
  let := hN
  exact (Atlas.GroupTheory.iwasawa_stabilizer_normal_subgroups
    (baseLine k) (lineRootClosure k) (lineRootClosure_le_stabilizer k)
    (lineRootClosure_normal_in_stabilizer k) hcomm
    (lineRootClosure_normalClosure_eq_top k) N).resolve_left hne

/-- Conditional root extraction. Final assembly must prove all three geometric inputs. -/
theorem exists_rootPoint_mem_of_singularLine_geometry
    (hfaith : FaithfulSMul (Points k) (SingularLines k))
    (hprimitive : MulAction.IsPreprimitive (Points k) (SingularLines k))
    (hcomm : IsMulCommutative (lineRootClosure k))
    (N : ClosedSubgroup (groupVariety k)) (hN : N.toSubgroup.Normal)
    (hdim : Variety.dimension N.carrierVariety ≠ 0) :
    ∃ (r : RootIndex) (a : k), a ≠ 0 ∧ rootPoint k r a ∈ N.toSubgroup := by
  have hne : N.toSubgroup ≠ ⊥ := by
    intro hbot
    have hfinite : Finite N.toSubgroup := by rw [hbot]; infer_instance
    have hpoints : Finite (Variety.Point N.carrierVariety) :=
      (Equiv.finite_iff N.pointEquiv).mpr hfinite
    exact hdim ((dimension_zero_iff_finite_points N.carrierVariety).mpr hpoints)
  have htop := normal_eq_top_of_singularLine_geometry k hfaith hprimitive hcomm
    N.toSubgroup hN hne
  exact ⟨simpleRoot 0, 1, one_ne_zero, htop ▸ Subgroup.mem_top _⟩

/-- Every positive-dimensional closed normal subgroup of the concrete Spin D4
carrier contains a nonidentity pinned root element. The singular-line geometry
and abelian relative root closure discharge all inputs to Iwasawa's argument. -/
theorem exists_rootPoint_mem
    (N : ClosedSubgroup (groupVariety k)) (hN : N.toSubgroup.Normal)
    (hdim : Variety.dimension N.carrierVariety ≠ 0) :
    ∃ (r : RootIndex) (a : k), a ≠ 0 ∧ rootPoint k r a ∈ N.toSubgroup :=
  exists_rootPoint_mem_of_singularLine_geometry k
    (singularLines_faithful k) (singularLines_preprimitive k)
    (lineRootClosure_isMulCommutative k) N hN hdim

end Triality.SimplyConnected.NormalRootExtraction
