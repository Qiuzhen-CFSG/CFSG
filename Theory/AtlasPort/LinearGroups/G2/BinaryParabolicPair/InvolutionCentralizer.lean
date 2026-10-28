module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Normalizers
public import Theory.SpecificGroups.DihedralSolvable
public import Mathlib.GroupTheory.Nilpotent

/-!
# A solvable involution centralizer in the actual group G₂(2)′

The distinguished long-root involution generates the entire highest-root
group over the two-element field. Its centralizer therefore normalizes that
root group and lies in the first parabolic. The reverse containment is the
existing root-coordinate centralization calculation, giving equality.
The parabolic is solvable: its normal five-root two-group has the explicit
six-element dihedral quotient constructed in `Levi`.

Restricting this equality to the actual octonion commutator subgroup identifies
the involution centralizer with `derivedFirst`. The involution belongs to the
chosen positive-root Sylow subgroup `derivedSylow`, providing the solvable
centralizer premise for Fong's wreathed Sylow recognition theorem.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), pp.69–76. The concrete carrier, root normalizer,
and parabolic quotient are inherited from the licensed ATLAS port through
the imports; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore

/-- The full binary octonion centralizer of the marked involution is the
first root-defined parabolic. -/
theorem centralizer_z_eq_firstParabolic :
    Subgroup.centralizer ({z} : Set (Model (ZMod 2))) = firstParabolic := by
  apply le_antisymm
  · have hp : LieParabolicSetup.parabolic₁ (F := ZMod 2) = firstParabolic := by
      unfold LieParabolicSetup.parabolic₁ firstParabolic
      rw [LieParabolicSetup.borel_eq_unipotent_of_card_two
        (by simp [Nat.card_eq_fintype_card])]
    rw [← hp, ← SylowParabolicInvariance.normalizer_highestRoot]
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
    rcases hb a.toAdd with h | h
    · change rootA a.toAdd * g = g * rootA a.toAdd
      rw [h, rootA_zero, one_mul, mul_one]
    · change rootA a.toAdd * g = g * rootA a.toAdd
      rw [h]
      exact Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)
  · intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr (firstParabolic_centralizes_z g hg)

/-- The first binary parabolic is an extension of a two-group by a dihedral
group of order six. -/
theorem firstParabolic_isSolvable : Group.IsSolvable firstParabolic := by
  let : Group.IsNilpotent core :=
    (IsPGroup.of_card (show Nat.card core = 2 ^ 5 from card_core)).isNilpotent
  let : Group.IsSolvable (core.subgroupOf firstParabolic) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe core_le_firstParabolic).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe core_le_firstParabolic).injective
  let : Group.IsSolvable (DihedralGroup 3) := GLS3.Chapter5.dihedralGroup_isSolvable 3
  let : Group.IsSolvable (firstParabolic ⧸ core.subgroupOf firstParabolic) :=
    Group.isSolvable_of_isSolvable_injective
      (f := firstParabolicQuotientEquiv.toMonoidHom) firstParabolicQuotientEquiv.injective
  exact (Group.isSolvable_iff_subgroup_quotient (core.subgroupOf firstParabolic)).mpr
    ⟨inferInstance, inferInstance⟩

/-- The distinguished long-root involution, in the actual commutator carrier. -/
def derivedInvolution : DerivedModel := ⟨z, rootA_one_mem_commutator⟩

/-- The chosen involution belongs to the concrete positive-root Sylow subgroup. -/
theorem derivedInvolution_mem_sylow : derivedInvolution ∈ derivedSylow := by
  change derivedInvolution ∈ (derivedSylow : Subgroup DerivedModel)
  rw [derivedSylow_eq]
  change rootA (1 : ZMod 2) ∈ unipotent
  exact Subgroup.subset_closure (by simp)

theorem derivedInvolution_order : orderOf derivedInvolution = 2 := by
  rw [← orderOf_injective DerivedModel.subtype DerivedModel.subtype_injective]
  exact z_order

/-- The centralizer inside G₂(2)′ is exactly the restricted first parabolic. -/
theorem centralizer_derivedInvolution_eq_first :
    Subgroup.centralizer ({derivedInvolution} : Set DerivedModel) = derivedFirst := by
  ext g
  change g ∈ Subgroup.centralizer ({derivedInvolution} : Set DerivedModel) ↔
    g.val ∈ firstParabolic
  rw [← centralizer_z_eq_firstParabolic, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- Solvability passes to the actual intersection with the commutator group. -/
theorem derivedFirst_isSolvable : Group.IsSolvable derivedFirst := by
  let : Group.IsSolvable firstParabolic := firstParabolic_isSolvable
  apply Group.isSolvable_of_isSolvable_injective
    (f := DerivedModel.subtype.subgroupComap firstParabolic)
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : firstParabolic => x.val) h

/-- The marked involution has a solvable centralizer in the derived group. -/
theorem isSolvable_centralizer_derivedInvolution :
    Group.IsSolvable (Subgroup.centralizer ({derivedInvolution} : Set DerivedModel)) := by
  rw [centralizer_derivedInvolution_eq_first]
  exact derivedFirst_isSolvable

/-- A concrete Sylow involution supplies Fong's solvable-centralizer premise. -/
theorem exists_involution_solvable_centralizer :
    ∃ x : DerivedModel, x ∈ derivedSylow ∧ orderOf x = 2 ∧
      Group.IsSolvable (Subgroup.centralizer ({x} : Set DerivedModel)) :=
  ⟨derivedInvolution, derivedInvolution_mem_sylow, derivedInvolution_order,
    isSolvable_centralizer_derivedInvolution⟩

end Atlas.G2.BinaryParabolicPair
