module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ThreeSpace
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals

/-!
# Ordinary fixed spaces do not give the G₂ plane orbit

The positive-root subgroup fixes only the first natural line. It embeds in
the point-parabolic residual, so some Sylow of that residual also has fixed
space contained in the line. Its fixed space in the third flag space cannot
be an orbit plane. The plane instead has the displacement characterization
modulo the first line proved in SylowFlag.displacement_mem_N1_iff.

This diagnoses the literal fixed-space interface suggested by the last
sentence of Aschbacher--Smith 11.1.4, printed p.765. It does not refute the
full ambient source theorem, whose conclusion is a normalizer containment.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.FixedPlane
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag Atlas.G2.LieParabolicSetup
open Subgroup Representation Representation.OneCohomology
variable (F : Type*) [Field F] [CharP F 2]

/-- The fixed space of an actual Sylow of the point residual (source L₁). -/
def pointSylowFixed (P : Sylow 2 (local₂ (F := F))) : Submodule F (Space F) :=
  fixed (((Natural.action F).comp local₂.subtype).comp (P : Subgroup local₂).subtype)

/-- The actual orbit of the natural plane under the point residual. -/
def planeOrbit : Set (Submodule F (Space F)) :=
  {W | ∃ g : local₂ (F := F), W = (naturalPlane F).map (Natural.action F g.val)}

/-- A Sylow of the point residual contains the derived positive-root subgroup,
and hence fixes at most the first natural line. -/
theorem exists_pointSylow_fixed_le_line [Finite F] :
    ∃ P : Sylow 2 (local₂ (F := F)), pointSylowFixed F P ≤ N1 F := by
  let j : U F →* local₂ (F := F) :=
    ((D F).subtype.comp (U F).subtype).codRestrict local₂
      (fun u => unipotent_le_local₂ u.property)
  have hj : IsPGroup 2 j.range :=
    (U_isTwoGroup F).of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hj.exists_le_sylow
  refine ⟨P,?_⟩
  rw [← natural_fixed]
  intro x hx
  change ∀ u : U F, derivedAction F u.val x = x
  intro u
  exact hx ⟨j u,hP (MonoidHom.mem_range.mpr ⟨u,rfl⟩)⟩

/-- Ordinary Sylow fixed subspaces of the third space cannot equal the plane orbit.
In particular replacing fixed spaces modulo V₁ by literal fixed subgroups is invalid. -/
theorem planeOrbit_ne_sylowFixed [Finite F] :
    planeOrbit F ≠ Set.range (fun P : Sylow 2 (local₂ (F := F)) =>
      naturalThreeSpace F ⊓ pointSylowFixed F P) := by
  intro he
  obtain ⟨P,hP⟩ := exists_pointSylow_fixed_le_line F
  have hm : naturalThreeSpace F ⊓ pointSylowFixed F P ∈ planeOrbit F := by
    rw [he]
    exact ⟨P,rfl⟩
  obtain ⟨g,hg⟩ := hm
  have hd := Submodule.finrank_mono
    ((inf_le_right : naturalThreeSpace F ⊓ pointSylowFixed F P ≤ _).trans hP)
  rw [hg,Transport.finrank_map, naturalPlane_finrank, N1_finrank] at hd
  omega

/-- The same failure for the literal solvable residual of the full point
parabolic, with the required nonbinary field hypothesis. -/
theorem residualPlaneOrbit_ne_sylowFixed [Finite F] (hq : 2 < Nat.card F) :
    let R : Subgroup (Model F) :=
      (solvableResidual (parabolic₂ (F := F))).map parabolic₂.subtype
    {W : Submodule F (Space F) |
      ∃ g : R, W = (naturalPlane F).map (Natural.action F g.val)} ≠
      Set.range (fun P : Sylow 2 R => naturalThreeSpace F ⊓
        fixed (((Natural.action F).comp R.subtype).comp (P : Subgroup R).subtype)) := by
  dsimp only
  rw [HigherFieldResiduals.parabolic₂_residual hq]
  exact planeOrbit_ne_sylowFixed F

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.FixedPlane
