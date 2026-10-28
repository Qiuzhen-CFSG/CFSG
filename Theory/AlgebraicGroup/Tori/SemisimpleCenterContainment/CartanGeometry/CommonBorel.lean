module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.CartanGeometry.FixedLocus
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.Tori.Basic


/-!
# A common Borel for a torus and a centralizing element

This is the complete fixed-locus argument of Borel, *Linear Algebraic Groups*,
§11.12 (`refs/KGroup/Bor1/Chapter4.tex`). The earlier §11.10 element-coverage
statement is the sole explicit geometric premise.

Choose a genuine complete Borel homogeneous-space model and use proved Borel
conjugacy to turn element coverage into a fixed point. The complete locus fixed
by that element has a torus fixed point by `FixedLocus`. Its stabilizer is an
actual conjugate of the chosen Borel, containing both the torus and the element.
All comparisons use the model's equivariant point equivalence to the actual
Plücker homogeneous space.
-/

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Bor1
open Theory.AlgebraicGroup.BorelGeometricConjugacy

universe u
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
set_option linter.style.haveILetI false

/-- Element coverage supplies a nonempty fixed locus in a genuine complete
Borel homogeneous space. Applying the solvable fixed-point theorem on that
locus puts the torus and its centralizing element in one Borel. -/
public theorem exists_common_borel_of_element_coverage
    (hcoverage : ∀ a : Variety.Point G,
      ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ a ∈ B)
    {S : ClosedSubgroup G} (hS : IsSubtorus S)
    (a : Variety.Point G) (ha : a ∈ S.centralizer) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ S ≤ B ∧ a ∈ B := by
  obtain ⟨Ba, hBa, haBa⟩ := hcoverage a
  obtain ⟨B₀, hB₀, ⟨M⟩⟩ := exists_borel_completeModel Ba hBa
  obtain ⟨g, hg⟩ := conjugacy hB₀ hBa
  rw [hg] at haBa
  have hafix : a • borelHomogeneousSpace.projection B₀ g =
      borelHomogeneousSpace.projection B₀ g := by
    apply Subtype.ext
    exact (projectivization_fixed_iff_mem_conjugate B₀ g a).mpr haBa
  have hne : ∃ x : Point M.variety, M.action.toMulAction.smul a x = x := by
    refine ⟨M.pointEquiv.symm (borelHomogeneousSpace.projection B₀ g), ?_⟩
    apply M.pointEquiv.injective
    rw [M.equivariant, Equiv.apply_symm_apply]
    exact hafix
  have hSsolv : Group.IsSolvable (Variety.Point S.carrierVariety) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hS.isMulCommutative)
  obtain ⟨x, hax, hSx⟩ := exists_common_fixedPoint_of_centralizes M.action
    M.complete S hS.isConnected hSsolv a ha hne
  let P := MulAction.stabilizer (Variety.Point G) (M.pointEquiv x)
  have hSP : S.toSubgroup ≤ P := by
    intro s hs
    change s • M.pointEquiv x = M.pointEquiv x
    rw [← M.equivariant, hSx s hs]
  have haP : a ∈ P := by
    change a • M.pointEquiv x = M.pointEquiv x
    rw [← M.equivariant, hax]
  have hle : S.toSubgroup ⊔ Subgroup.zpowers a ≤ P :=
    sup_le hSP (Subgroup.zpowers_le_of_mem haP)
  obtain ⟨b, hb⟩ := subgroup_le_conjugate_of_homogeneousSpace_fixed B₀
    (S.toSubgroup ⊔ Subgroup.zpowers a) (M.pointEquiv x) (fun s hs => hle hs)
  exact ⟨B₀.conjugate b, hB₀.conjugate b,
    (fun s hs => hb ((show S.toSubgroup ≤ S.toSubgroup ⊔ Subgroup.zpowers a from
      le_sup_left) hs)), hb ((show Subgroup.zpowers a ≤
        S.toSubgroup ⊔ Subgroup.zpowers a from le_sup_right) (Subgroup.mem_zpowers a))⟩

end Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
