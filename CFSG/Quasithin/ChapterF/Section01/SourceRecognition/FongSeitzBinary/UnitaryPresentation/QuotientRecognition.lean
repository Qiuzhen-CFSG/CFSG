module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.QuotientData
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.KernelTrapping
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveMarkings
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourMarkings
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveDescent
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.CoreFree

/-!
# Whole projective unitary recognition on the same marked quotient

The constructed onto model maps send positive roots into source U and the
full torus into B∩N. Marked source Weyl classes separate their eight Bruhat
cells, so the full Borel preimage is exactly the model Borel. Normality
kills the SU₄ kernel; for SU₅ it identifies the kernel with the canonical
projective scalars when the target center is trivial. The same map sends
both entire model parabolics to the prescribed source endpoints, in either
orientation. Field reconstruction, equations and generation remain explicit
source duties; source centerlessness is discharged by the local application.
Source: DGS, Groups and Graphs, Theorem D, printed p.224; Steinberg,
Lectures on Chevalley Groups, Theorems 4 and 33.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {X E : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
variable {P : Fin 2 → Subgroup X} {Q : MarkedQuotient P} {split : SplitData Q.tits} {i : Fin 2}

namespace FourData
open Theory.SpecificGroups.ClassicalUnitary UnitaryFourFlag
variable (σ : E ≃+* E) (hσ : Function.Involutive σ) (d : FourData Q split i σ hσ)
variable (hm : rotationOrder Q=4)
local notation "J" => form E σ hσ
local notation "BB" => borelSU E J

theorem modelHom_s : d.modelHom σ hσ (FourWeyl.s E σ hσ)=(d.lifts.s : X ⧸ Q.D) :=
  d.modelHom_generator σ hσ .s

theorem modelHom_t : d.modelHom σ hσ (FourWeyl.t E σ hσ)=(d.lifts.t : X ⧸ Q.D) :=
  d.modelHom_generator σ hσ .t

include hm in
theorem modelHom_weyl_separated (w : WeylWord)
    (hw : d.modelHom σ hσ (w.eval (FourWeyl.s E σ hσ) (FourWeyl.t E σ hσ))∈Q.tits.B) : w=.one := by
  rw [WeylWord.map_eval,d.modelHom_s,d.modelHom_t] at hw
  exact (MarkedWeyl.Lifts.eval_mem_borel_iff Q hm i d.lifts w).mp hw

include hm in
theorem modelHom_borel_comap : Q.tits.B.comap (d.modelHom σ hσ)=BB := by
  apply borel_comap_of_cells _ _ _ (FourWeyl.s E σ hσ) (FourWeyl.t E σ hσ)
    (FourCells.all_eight_cells E σ hσ) _ (d.modelHom_weyl_separated σ hσ hm)
  rw [←FourCells.borel_eq E σ hσ]
  exact d.modelHom_borel_le σ hσ

include hm in
theorem modelHom_borel : (BB).map (d.modelHom σ hσ)=Q.tits.B := by
  rw [←d.modelHom_borel_comap σ hσ hm]
  exact map_comap_eq_self_of_surjective (d.modelHom_surjective σ hσ) _

include hm in
theorem modelHom_kernel_le : (d.modelHom σ hσ).ker≤BB := by
  rw [←d.modelHom_borel_comap σ hσ hm]
  intro g hg
  change d.modelHom σ hσ g∈Q.tits.B
  rw [show d.modelHom σ hσ g=1 from hg]
  exact Q.tits.B.one_mem

include hm in
theorem modelHom_injective : Function.Injective (d.modelHom σ hσ) :=
  (MonoidHom.ker_eq_bot_iff _).mp
    (UnitaryFourSylow.eq_bot_of_normal_le_borel E σ hσ _ (d.modelHom_kernel_le σ hσ hm))

/-- The presentation and source Weyl classes construct the whole SU₄ comparison. -/
def equiv : (J).specialSubgroup ≃* (X ⧸ Q.D) :=
  MulEquiv.ofBijective (d.modelHom σ hσ) ⟨d.modelHom_injective σ hσ hm,d.modelHom_surjective σ hσ⟩

include hm in
theorem modelHom_point : (pointParabolicSU E J).map (d.modelHom σ hσ)=
    Q.tits.standardParabolic {Q.simple i} := by
  rw [FourCells.point_eq_generated,Subgroup.map_sup,MonoidHom.map_closure,Set.image_singleton,
    d.modelHom_t,d.modelHom_borel σ hσ hm]
  exact (MarkedWeyl.Lifts.simple_parabolic Q i d.lifts.t d.lifts.t_class).symm

include hm in
theorem modelHom_plane : (planeParabolicSU E J).map (d.modelHom σ hσ)=
    Q.tits.standardParabolic {Q.simple (1-i)} := by
  rw [FourCells.plane_eq_generated,Subgroup.map_sup,MonoidHom.map_closure,Set.image_singleton,
    d.modelHom_s,d.modelHom_borel σ hσ hm]
  exact (MarkedWeyl.Lifts.simple_parabolic Q (1-i) d.lifts.s d.lifts.s_class).symm

/-- The actual projective carrier, via the canonical injective SU₄ projection. -/
def projectiveEquiv : PSU E J ≃* (X ⧸ Q.D) :=
  (MulEquiv.ofBijective (project E J) ⟨project_injective E J,project_surjective E J⟩).symm.trans
    (d.equiv σ hσ hm)

@[simp] theorem projectiveEquiv_project (g : (J).specialSubgroup) :
    d.projectiveEquiv σ hσ hm (project E J g)=d.modelHom σ hσ g := by
  change d.equiv σ hσ hm ((MulEquiv.ofBijective (project E J)
    ⟨project_injective E J,project_surjective E J⟩).symm
      ((MulEquiv.ofBijective (project E J) ⟨project_injective E J,project_surjective E J⟩) g))=_
  rw [MulEquiv.symm_apply_apply]
  rfl
end FourData

namespace FiveData
open Theory.SpecificGroups.UnitaryFive
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
variable (d : FiveData Q split i J) (hm : rotationOrder Q=4)
local notation "BB" => PositiveMaps.borel (FivePositive.roots J κ hκ hJ) (FiveWeyl.h J κ hκ hJ)

theorem modelHom_s : d.modelHom J κ hκ hJ (FiveWeyl.s J κ hκ hJ)=(d.lifts.s : X ⧸ Q.D) :=
  d.modelHom_generator J κ hκ hJ .s

theorem modelHom_t : d.modelHom J κ hκ hJ (FiveWeyl.t J κ hκ hJ)=(d.lifts.t : X ⧸ Q.D) :=
  d.modelHom_generator J κ hκ hJ .t

include hm in
theorem modelHom_weyl_separated (w : WeylWord)
    (hw : d.modelHom J κ hκ hJ (w.eval (FiveWeyl.s J κ hκ hJ) (FiveWeyl.t J κ hκ hJ))∈Q.tits.B) : w=.one := by
  rw [WeylWord.map_eval,d.modelHom_s,d.modelHom_t] at hw
  exact (MarkedWeyl.Lifts.eval_mem_borel_iff Q hm i d.lifts w).mp hw

include hm in
theorem modelHom_borel_comap : Q.tits.B.comap (d.modelHom J κ hκ hJ)=BB :=
  borel_comap_of_cells _ _ _ (FiveWeyl.s J κ hκ hJ) (FiveWeyl.t J κ hκ hJ)
    (FiveCells.all_eight_cells J κ hκ hJ) (d.modelHom_borel_le J κ hκ hJ)
    (d.modelHom_weyl_separated J κ hκ hJ hm)

include hm in
theorem modelHom_borel : (BB).map (d.modelHom J κ hκ hJ)=Q.tits.B := by
  rw [←d.modelHom_borel_comap J κ hκ hJ hm]
  exact map_comap_eq_self_of_surjective (d.modelHom_surjective J κ hκ hJ) _

include hm in
theorem modelHom_kernel_le : (d.modelHom J κ hκ hJ).ker≤BB := by
  rw [←d.modelHom_borel_comap J κ hκ hJ hm]
  intro g hg
  change d.modelHom J κ hκ hJ g∈Q.tits.B
  rw [show d.modelHom J κ hκ hJ g=1 from hg]
  exact Q.tits.B.one_mem

variable (hZ : center (X ⧸ Q.D)=⊥)

include hm hZ in
/-- The kernel is EXACTLY that of the literal SU₅→PSU₅ map at every q. -/
theorem modelHom_kernel : (d.modelHom J κ hκ hJ).ker=(project J).ker :=
  FiveCells.kernel_eq_project_kernel J κ hκ hJ (d.modelHom J κ hκ hJ)
    (d.modelHom_surjective J κ hκ hJ) hZ (d.modelHom_kernel_le J κ hκ hJ hm)

/-- The projective comparison is constructed from the equations, generation,
source Weyl markings and centerlessness, never from a supplied model map. -/
def projectiveEquiv : ProjectiveSpecialUnitaryMatrixGroup J ≃* (X ⧸ Q.D) :=
  FiveCells.projectiveEquiv J κ hκ hJ (d.modelHom J κ hκ hJ)
    (d.modelHom_surjective J κ hκ hJ) hZ (d.modelHom_kernel_le J κ hκ hJ hm)

@[simp] theorem projectiveEquiv_project (g : (J).specialSubgroup) :
    d.projectiveEquiv J κ hκ hJ hm hZ (project J g)=d.modelHom J κ hκ hJ g :=
  FiveCells.projectiveEquiv_project J κ hκ hJ (d.modelHom J κ hκ hJ)
    (d.modelHom_surjective J κ hκ hJ) hZ (d.modelHom_kernel_le J κ hκ hJ hm) g

include hm in
theorem modelHom_line : (specialStabilizer J (line E)).map (d.modelHom J κ hκ hJ)=
    Q.tits.standardParabolic {Q.simple i} := by
  rw [FiveCells.line_eq_generated J κ hκ hJ,Subgroup.map_sup,MonoidHom.map_closure,Set.image_singleton,
    d.modelHom_t,d.modelHom_borel J κ hκ hJ hm]
  exact (MarkedWeyl.Lifts.simple_parabolic Q i d.lifts.t d.lifts.t_class).symm

include hm in
theorem modelHom_plane : (specialStabilizer J (plane E)).map (d.modelHom J κ hκ hJ)=
    Q.tits.standardParabolic {Q.simple (1-i)} := by
  rw [FiveCells.plane_eq_generated J κ hκ hJ,Subgroup.map_sup,MonoidHom.map_closure,Set.image_singleton,
    d.modelHom_s,d.modelHom_borel J κ hκ hJ hm]
  exact (MarkedWeyl.Lifts.simple_parabolic Q (1-i) d.lifts.s d.lifts.s_class).symm
end FiveData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
