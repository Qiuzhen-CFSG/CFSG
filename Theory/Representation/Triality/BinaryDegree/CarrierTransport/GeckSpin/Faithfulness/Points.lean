module
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.CliffordComparison
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalNaturalIrreducibility
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Tactic

/-!
# Detection of Spin points by the Geck Clifford coordinates

Fixing the root bivectors fixes the actual Clifford root units. Root generation
then gives a central Spin point. Its natural action commutes with the split
Omega representation, so a nonzero eigenspace and natural irreducibility force
a scalar action. Preservation of a norm-one vector makes the scalar square one;
in characteristic two it is one. Faithfulness of the natural action finishes.

This proves the `hfaith` input to `GeckSpin.exists_finite_comparison_of_clifford`.
It uses neither the Geck root-intertwining identities nor coordinate injectivity.
Source: GLS3, §§1.12–1.14, especially the adjoint kernel in 1.14.9(c), and §2.7.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin
open Theory.AlgebraicGroup Triality.SimplyConnected Triality.SimplyConnected.Pinning
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

private theorem conjugation_one (x : Points k) : pointConjugation k x 1 = 1 := by
  simp only [pointConjugation_apply, mul_one]
  change ((pointEquiv k x * pointEquiv k x⁻¹ : spinGroup (quadraticForm k)) : Clifford k) = 1
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

private theorem commute_root_of_fixed (x : Points k) (r : RootIndex)
    (h : pointConjugation k x (rootBivector k r) = rootBivector k r) (t : k) :
    Commute x (rootPoint k r t) := by
  have hc : x * rootPoint k r t * x⁻¹ = rootPoint k r t := by
    apply (pointEquiv k).injective
    apply Subtype.ext
    simp only [map_mul]
    change pointConjugation k x (pointEquiv k (rootPoint k r t) : Clifford k) =
      (pointEquiv k (rootPoint k r t) : Clifford k)
    rw [rootPoint_clifford, map_add, map_smul, conjugation_one, h]
  exact (mul_inv_eq_iff_eq_mul.mp hc : x * rootPoint k r t = rootPoint k r t * x)

private theorem commute_all_of_fixed (x : Points k)
    (h : ∀ r, pointConjugation k x (rootBivector k r) = rootBivector k r) :
    ∀ y : Points k, Commute x y := by
  have hc : allRootPointSubgroup k ≤ Subgroup.centralizer {x} := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨r,t⟩,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    exact (commute_root_of_fixed k x r (h r) t).eq
  rw [allRootPointSubgroup_eq_top] at hc
  intro y
  exact Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_top y)) x (by simp)

private theorem eq_one_of_commute_all (x : Points k)
    (hc : ∀ y : Points k, Commute x y) : x = 1 := by
  let F : Module.End k (QuadraticSpace k) := (naturalAction k x).1.toLinearMap
  obtain ⟨a, ha⟩ := F.exists_eigenvalue
  have hcomm (g : OmegaPoints k) (v : QuadraticSpace k) :
      F (g.1.1 v) = g.1.1 (F v) := by
    obtain ⟨y, rfl⟩ := toOmega_surjective k g
    have hh := congrArg (fun e : quadraticIsometrySubgroup (quadraticForm k) => e.1 v)
      (congrArg (naturalAction k) (hc y).eq)
    simpa only [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, naturalAction,
      MonoidHom.comp_apply, Subgroup.subtype_apply, F, LinearEquiv.coe_coe] using hh
  let s := standardHyperbolicSplit (k := k) 4
  have hinv : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s)
      (F.eigenspace a) := by
    intro g v hv
    have hact := evenOrthogonalNaturalRepresentation_action_linear_points s (by simp [s]) g
    have hactv (w : QuadraticSpace k) :
        ((evenOrthogonalNaturalRepresentation s).action g : Module.End k _) w =
          (evenSpinActionImageClosedSubgroupPoints _ s (by simp [s]) g).1.1 w :=
      LinearEquiv.congr_fun hact w
    change ((evenOrthogonalNaturalRepresentation s).action g : Module.End k _) v ∈ _
    rw [hactv]
    apply Module.End.mem_eigenspace_iff.mpr
    rw [hcomm, Module.End.mem_eigenspace_iff.mp hv, map_smul]
  have htop : F.eigenspace a = ⊤ := by
    rcases evenOrthogonalNaturalRepresentation_isAlgebraicallyIrreducible s
      (by simp [s]) (F.eigenspace a) hinv with hb | ht
    · exact False.elim (ha hb)
    · exact ht
  have hscalar (v : QuadraticSpace k) : F v = a • v := by
    apply Module.End.mem_eigenspace_iff.mp
    rw [htop]
    exact Submodule.mem_top
  have hsquare : a * a = 1 := by
    let v : QuadraticSpace k := (Pi.single 0 1, Pi.single 0 1)
    have hv : quadraticForm k v = 1 := by simp [v, quadraticForm, hyperbolicForm_apply, Pi.single_apply]
    have hh := (mem_quadraticIsometrySubgroup (quadraticForm k) _).mp
      (naturalAction k x).property v
    change quadraticForm k (F v) = quadraticForm k v at hh
    rw [hscalar, QuadraticMap.map_smul, hv] at hh
    simpa [smul_eq_mul] using hh
  have ha1 : a = 1 := by
    rcases mul_self_eq_one_iff.mp hsquare with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply naturalAction_injective k
  rw [map_one]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change F v = v
  simpa only [ha1, one_smul] using hscalar v

/-- Clifford conjugation on the literal comparison coordinates detects Spin points. -/
public theorem pointConjugation_ext (x y : Points k)
    (h : ∀ v : Coordinates k,
      pointConjugation k x (embedding k v) = pointConjugation k y (embedding k v)) :
    x = y := by
  let : DecidableEq Index := indexDecidableEq
  have hfix (v : Coordinates k) :
      pointConjugation k (y⁻¹ * x) (embedding k v) = embedding k v := by
    rw [map_mul, Module.End.mul_apply, h, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hroot (r : RootIndex) :
      pointConjugation k (y⁻¹ * x) (rootBivector k r) = rootBivector k r := by
    simpa only [embedding_single, basisImage, one_smul] using hfix (Pi.single (.inr r) 1)
  have he := eq_one_of_commute_all k _ (commute_all_of_fixed k _ hroot)
  exact (inv_mul_eq_one.mp he).symm
end Triality.BinaryDegree.CarrierTransport.GeckSpin
