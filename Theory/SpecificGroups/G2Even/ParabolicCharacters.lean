module
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Borel

/-!
# A scalar character of the short G₂ parabolic and solvable Sylow normalizers

The determinant of the action on the standard null plane lifts to the field
units. The diagonal element with torus coordinates (a,1) realizes every unit.
Conjugacy transports the proved solvability of the standard Borel to the
normalizer of every Sylow two-subgroup, including the binary field.
The long parabolic's scalar quotient is already supplied by the public
lineScalarHom on its identified point stabilizer.

Source: the full rank-one parabolics used in Aschbacher--Smith C.2.7,
pp.145--147. The octonion coordinates extend the licensed ATLAS model;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.ParabolicCharacters
open Atlas.SplitOctonion Atlas.G2.Explicit LieParabolicSetup
variable {F : Type*} [Field F]

def shortScalar : parabolic₁ (F := F) →* Fˣ :=
  (shortDet.comp (Subgroup.inclusion parabolic₁_le_shortPlaneStabilizer)).toHomUnits

theorem shortScalar_surjective : Function.Surjective (shortScalar (F := F)) := by
  intro a
  have ht : torus a 1 ∈ parabolic₁ (F := F) :=
    borel_le_parabolic₁ (show torus a 1 ∈ borel from
      (show splitTorus ≤ borel (K := F) from le_sup_right) ⟨(a,1),rfl⟩)
  refine ⟨⟨torus a 1,ht⟩,?_⟩
  apply Units.ext
  change (shortRepresentation ⟨torus a 1,parabolic₁_le_shortPlaneStabilizer ht⟩).det = a.val
  rw [Matrix.det_fin_two]
  change (torus a 1).val (basisVector 0) 0 * (torus a 1).val (basisVector 1) 1 -
    (torus a 1).val (basisVector 1) 0 * (torus a 1).val (basisVector 0) 1 = a.val
  simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]

variable [CharP F 2]

open Subgroup
variable [Finite F]
theorem sylow_normalizer_isSolvable (S : Sylow 2 (Model F)) :
    Group.IsSolvable (normalizer (S : Set (Model F))) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  have hm : (S : Subgroup (Model F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  have hn : (normalizer (S : Set (Model F))).map (MulAut.conj g).toMonoidHom = borel := by
    change (normalizer ((S : Subgroup (Model F)) : Set (Model F))).map _ = _
    rw [map_equiv_normalizer_eq,hm,SylowNormalizer.normalizer_unipotent]
  let e := ((MulAut.conj g).subgroupMap (normalizer (S : Set (Model F)))).trans
    (MulEquiv.subgroupCongr hn)
  let : Group.IsSolvable (borel (K := F)) := DerivedNormalizerSolvable.isSolvable_borel
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
end Atlas.G2.ParabolicCharacters
