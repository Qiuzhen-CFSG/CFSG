module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Model.Calculation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Marking.Construction

/-!
# First-core nonquadraticity from the nonzero residual triple

The source quotient is Y_d/Z_alpha with its actual conjugation action.
The original vertex core kills that action, so a compatible marking
descends it to S4. The first layer generates this quotient under the
opposite actor and is fixed by the first core. A finite S4 calculation
then turns first-core quadraticity into full-actor fixation of the
opposite-core displacements, contradicting the given residual triple.

The final theorem constructs the compatible parabolic marking and the literal
elementary quotient, then applies the universal binary S4 calculation. Its
only nonzero-triple premise is the source triple supplied by
`Y_core_residual_triple_not_le` from the preparatory data in the parent
assembly. No module, marking or calculation premise remains.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), pp.905--907,
especially the nonzero triple in claim (3) on p.906.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Nonquadratic
universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}

/-- The marked binary calculation excludes first-core quadraticity on the
actual auxiliary span. Both extra inputs remain explicit. -/
theorem Y_first_core_not_quadratic_of_marking_and_calculation
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d)
    (htriple : ¬ ⁅⁅Y source i d,localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R))
    (b : SourceModule source i d) (marking : ParabolicMarking source i d)
    (hcalc : ∀ (ρ : Representation (ZMod 2) S4Model.Actor b.Space)
        (D : Submodule (ZMod 2) b.Space),
      (∀ a ∈ S4Model.firstCore, ∀ v ∈ D, ρ a v = v) →
      orbitSpan ρ D = ⊤ → QuadraticOn ρ S4Model.firstCore →
      DisplacementsFixed ρ S4Model.oppositeCore) :
    ¬ ⁅⁅Y source i d,Q R (beta R)⁆,Q R (beta R)⁆ ≤ Z R (alpha R) := by
  intro hquad
  have hkill : marking.hom.ker ≤ b.representation.ker := by
    rw [marking.kernel]
    exact b.core_le_kernel geometry early
  have hkill' : marking.hom.ker ≤ b.representation.asGroupHom.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    exact hkill ha
  let τ : S4Model.Actor →* Units (Module.End (ZMod 2) b.Space) :=
    marking.hom.liftOfSurjective marking.onto ⟨b.representation.asGroupHom, hkill'⟩
  have hτ (a : localFlagActor source (!i) d) :
      τ (marking.hom a) = b.representation.asGroupHom a :=
    marking.hom.liftOfRightInverse_comp_apply _ _ ⟨b.representation.asGroupHom, hkill'⟩ a
  let ρ : Representation (ZMod 2) S4Model.Actor b.Space := (Units.coeHom _).comp τ
  have hρ (a : localFlagActor source (!i) d) : ρ (marking.hom a) = b.representation a := by
    change ↑(τ (marking.hom a)) = b.representation a
    rw [hτ]
    exact b.representation.asGroupHom_apply a
  let D := b.image (V R (beta R))
  have hfixed : ∀ a ∈ S4Model.firstCore, ∀ v ∈ D, ρ a v = v := by
    intro a ha v hv
    rw [← marking.first_image] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [hρ]
    exact b.first_fixed geometry common early hkernel x hx v hv
  have hspan : orbitSpan ρ D = ⊤ := by
    have h : orbitSpan b.representation D ≤ orbitSpan ρ D := by
      apply iSup_le
      intro a
      apply le_iSup_of_le (marking.hom a)
      rw [hρ]
    rw [b.first_orbit_eq_top geometry common.large_distance hkernel hd] at h
    exact top_unique h
  have hq : QuadraticOn ρ S4Model.firstCore := by
    have hsource := b.quadratic_of_commutator (flagKernel source i)
      (show ⁅⁅Y source i d,flagKernel source i⁆,flagKernel source i⁆ ≤ Z R (alpha R) from
        by rw [hkernel]; exact hquad)
    intro a ha c hc v
    rw [← marking.first_image] at ha hc
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hc
    simpa only [hρ] using hsource x hx y hy v
  have hf := hcalc ρ D hfixed hspan hq
  have hsource : DisplacementsFixed b.representation
      ((localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d)) := by
    intro a k hk v
    have hmk : marking.hom k ∈ S4Model.oppositeCore := by
      rw [← marking.opposite_image]
      exact mem_map_of_mem marking.hom hk
    simpa only [hρ] using hf (marking.hom a) (marking.hom k) hmk v
  apply htriple
  exact (commutator_mono le_rfl (map_mono (flagResidual_le source (!i)))).trans
    (b.triple_le_of_displacementsFixed (localFlagKernel source (!i) d)
      (map_mono (flagKernel_le source (!i))) hsource)

/-- The first core cannot act quadratically on the neighboring auxiliary span
modulo Z_alpha when the actual opposite-core residual triple is nonzero.
This supplies the nonquadraticity input of
`middle_left_index_le_two_of_derived_of_nonquadratic`. -/
theorem Y_first_core_not_quadratic
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d)
    (htriple : ¬ ⁅⁅Y source i d, localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    ¬ ⁅⁅Y source i d, Q R (beta R)⁆, Q R (beta R)⁆ ≤ Z R (alpha R) := by
  obtain ⟨marking⟩ := exists_parabolicMarking source i d hd
  exact Y_first_core_not_quadratic_of_marking_and_calculation
    source geometry common early i hkernel d hd htriple
    (sourceModule source geometry common early i d) marking
    S4Model.displacementsFixed_of_quadratic

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
