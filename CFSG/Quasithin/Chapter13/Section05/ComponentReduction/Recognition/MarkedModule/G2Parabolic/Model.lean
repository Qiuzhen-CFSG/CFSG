module

public import Theory.Representation.G2OrthogonalCover.RootGeometry
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualAction
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The seven-dimensional parabolic calculation in 13.5.21

The actual two-residual of the binary null-plane parabolic contains the
marked cubic and the right quaternion generator. Two explicit displacement
sources express every trace-zero octonion as a sum of their displacements.
Thus the residual generates the entire orthogonal cover, including its
scalar line. A calculation only on the six-dimensional natural quotient
would not establish this conclusion.

Source: Aschbacher–Smith, Lemma 13.5.21(6), printed p.924 / PDF p.941,
and I.2.3. Coordinates and the residual identification use the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
No additional upstream source is copied.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Natural Atlas.G2.BinaryParabolicPair Atlas.SplitOctonion
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Model
abbrev Actor := commutator (Model (ZMod 2))
abbrev Seven := TraceZero (ZMod 2)
abbrev residual := (pResidual 2 derivedFirst).map derivedFirst.subtype

private def cubicSource (x : Seven) : Seven :=
  ⟨![x.val 0 + x.val 1, x.val 0, x.val 2 + x.val 5, 0, 0,
    x.val 3 + x.val 5, x.val 6 + x.val 7, x.val 6], by simp [trace]⟩
private def quaternionSource (x : Seven) : Seven :=
  ⟨![0,0,0,0,0,0,x.val 2 + x.val 3 + x.val 5,0], by simp [trace]⟩
private def cubic : Actor := ⟨cubicActor, cubicActor_mem_derived⟩
private def quaternion : Actor := ⟨ResidualAction.right (QuaternionGroup.a 1),
  ResidualAction.K_le_derived (ResidualAction.right_mem _)⟩

private theorem cubic_mem_residual : cubic ∈ residual := by
  have hc := ResidualAction.derived_residual.ge ResidualAction.cubic_mem
  obtain ⟨c,hc,he⟩ := hc
  exact (show c = cubic from Subtype.ext he) ▸ hc

private theorem quaternion_mem_residual : quaternion ∈ residual := by
  have hc := ResidualAction.derived_residual.ge (ResidualAction.right_mem (QuaternionGroup.a 1))
  obtain ⟨c,hc,he⟩ := hc
  exact (show c = quaternion from Subtype.ext he) ▸ hc

private def vector (a : Fin 7 → ZMod 2) : Seven :=
  ⟨![a 0,a 1,a 2,a 3,a 3,a 4,a 5,a 6], by
    change a 3 + a 3 = 0
    exact CharTwo.add_self_eq_zero _⟩
private def basisVector (i : Fin 7) : Seven := vector (Pi.single i 1)
private def coordinates (x : Seven) : Fin 7 → ZMod 2 :=
  ![x.val 0,x.val 1,x.val 2,x.val 3,x.val 5,x.val 6,x.val 7]

private theorem basis_expansion (x : Seven) :
    ∑ i : Fin 7, coordinates x i • basisVector i = x := by
  have hd : x.val 3 = x.val 4 := by
    have ht : x.val 3 + x.val 4 = 0 := x.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left ht
  apply Subtype.ext
  ext j
  fin_cases j <;> simp [Fin.sum_univ_succ,basisVector,vector,coordinates,Pi.single_apply,hd]

set_option maxRecDepth 10000 in
private theorem displacement_basis : ∀ i : Fin 7,
    OrthogonalCover.action (ZMod 2) cubic (cubicSource (basisVector i)) - cubicSource (basisVector i) +
      (OrthogonalCover.action (ZMod 2) quaternion (quaternionSource (basisVector i)) -
        quaternionSource (basisVector i)) = basisVector i := by decide +kernel

/-- The actual two-residual generates the entire seven-dimensional cover. -/
theorem residual_generates_seven :
    subspaceCommutator (OrthogonalCover.action (ZMod 2)) ⊤ residual = ⊤ := by
  have hb (i : Fin 7) : basisVector i ∈
      subspaceCommutator (OrthogonalCover.action (ZMod 2)) ⊤ residual := by
    rw [← displacement_basis i]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨cubic, cubic_mem_residual, cubicSource (basisVector i), trivial, rfl⟩)
      (Submodule.subset_span ⟨quaternion, quaternion_mem_residual, quaternionSource (basisVector i), trivial, rfl⟩)
  apply top_unique
  intro x _
  rw [← basis_expansion x]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hb i))
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Model
