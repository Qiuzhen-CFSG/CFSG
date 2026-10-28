module

public import Theory.SpecificGroups.SymplecticFour.Flag
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Determinant kernels in the two symplectic four-space parabolics

Restriction to the stabilized line or plane gives a determinant character.
Its kernel is normal in that parabolic, and its image in the original matrix
group is the chosen local factor. Their intersection defines the unipotent
flag subgroup. Over a field of order two the unit group is trivial, so the
local factors equal their parabolics and the unipotent subgroup is the whole
overlap. The Sylow property and nonbinary local structure are separate results.

Source: the concrete local factors for Aschbacher--Smith F.1.12(I)(2),
printed pp.262--264. No ambient normality in Sp₄ is asserted.
-/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

/-- Restriction of the natural action to a stabilized subspace. -/
def restriction (W : Submodule F (Vector F)) :
    stabilizer W →* (W ≃ₗ[F] W) where
  toFun g := (toLinear g.val).ofSubmodules W W g.property
  map_one' := by
    ext x : 1
    apply Subtype.ext
    exact one_smul (Sp F) x.val
  map_mul' g h := by
    ext x : 1
    apply Subtype.ext
    exact mul_smul g.val h.val x.val

@[simp] theorem restriction_apply (W : Submodule F (Vector F))
    (g : stabilizer W) (x : W) : (restriction W g x).val = g.val • x.val := rfl

/-- The determinant on the stabilized subspace, with values in the field units. -/
def determinantCharacter (W : Submodule F (Vector F)) : stabilizer W →* Fˣ :=
  LinearEquiv.det.comp (restriction W)

/-- The determinant-one local factor, embedded in the original matrix group. -/
def determinantKernel (W : Submodule F (Vector F)) : Subgroup (Sp F) :=
  (determinantCharacter W).ker.map (stabilizer W).subtype

theorem determinantKernel_le (W : Submodule F (Vector F)) :
    determinantKernel W ≤ stabilizer W := by
  rintro g ⟨x, _, rfl⟩
  exact x.property

theorem determinantKernel_subgroupOf (W : Submodule F (Vector F)) :
    (determinantKernel W).subgroupOf (stabilizer W) = (determinantCharacter W).ker := by
  ext x
  exact Subgroup.mem_map_iff_mem (stabilizer W).subtype_injective

/-- Normality is inside the parabolic, not in Sp₄. -/
instance determinantKernel_normal (W : Submodule F (Vector F)) :
    ((determinantKernel W).subgroupOf (stabilizer W)).Normal := by
  rw [determinantKernel_subgroupOf]
  infer_instance

/-- The local factor in the point parabolic, not the full parabolic. -/
def pointLocal : Subgroup (Sp F) := determinantKernel (point F)

/-- The local factor in the plane parabolic, not the full parabolic. -/
def planeLocal : Subgroup (Sp F) := determinantKernel (plane F)

theorem pointLocal_le : pointLocal (F := F) ≤ pointParabolic :=
  determinantKernel_le _

theorem planeLocal_le : planeLocal (F := F) ≤ planeParabolic :=
  determinantKernel_le _

instance pointLocal_normal : ((pointLocal (F := F)).subgroupOf pointParabolic).Normal :=
  determinantKernel_normal _

instance planeLocal_normal : ((planeLocal (F := F)).subgroupOf planeParabolic).Normal :=
  determinantKernel_normal _

/-- With two field elements there is no torus character left in either parabolic. -/
theorem determinantKernel_eq_of_card_two [Finite F] (hF : Nat.card F = 2)
    (W : Submodule F (Vector F)) : determinantKernel W = stabilizer W := by
  have hc : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  have : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hc).1
  apply le_antisymm (determinantKernel_le W)
  intro g hg
  exact ⟨⟨g, hg⟩, Subsingleton.elim _ _, rfl⟩

theorem pointLocal_eq_of_card_two [Finite F] (hF : Nat.card F = 2) :
    pointLocal (F := F) = pointParabolic := determinantKernel_eq_of_card_two hF _

theorem planeLocal_eq_of_card_two [Finite F] (hF : Nat.card F = 2) :
    planeLocal (F := F) = planeParabolic := determinantKernel_eq_of_card_two hF _

/-- The determinant-one subgroup of the full flag stabilizer. The Sylow
property in characteristic two is a separate cardinality theorem. -/
def unipotent : Subgroup (Sp F) := pointLocal ⊓ planeLocal

theorem unipotent_le_borel : unipotent (F := F) ≤ borel :=
  inf_le_inf pointLocal_le planeLocal_le

theorem unipotent_eq_borel_of_card_two [Finite F] (hF : Nat.card F = 2) :
    unipotent (F := F) = borel := by
  rw [unipotent, pointLocal_eq_of_card_two hF, planeLocal_eq_of_card_two hF]
  rfl

end Theory.SpecificGroups.SymplecticFour
