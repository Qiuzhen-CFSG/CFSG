module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Escape
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Original embeddings and attained generation in the non-Bender branch

The orbit join is the literal I T inside the involution centralizer. Its
component condition and SQTK hypothesis are inherited along those exact
inclusions. The chosen involution lies in every parabolic over the original
Sylow, so its order proves that parameter-one E-generation is attained at
the numeric parameter one. No quotient-parameter equality is used.

Source: Aschbacher--Smith 10.3.3, printed p.756, and E.1.11, p.213.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- The component-orbit join stays in the original involution centralizer. -/
theorem orbit_join_le_centralizer (d : CentralizerData T D s) {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G))) :
    componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) ≤
      centralizer ({d.first * d.second} : Set G) := by
  rw [componentOrbit_sup]
  exact sup_le hI.1 d.sylow_le_centralizer

/-- The actual centralizer component is still a component of its Sylow join. -/
theorem component_in_orbit_join (d : CentralizerData T D s) {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G))) :
    I ∈ Chapter1.cComponentsIn
      (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G)) := by
  have hIJ : I ≤ componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) :=
    (le_componentOrbit I (T : Subgroup G)).trans le_sup_left
  exact ⟨hIJ, hI.2.subgroupOf_of_le hIJ (orbit_join_le_centralizer d hI)⟩

/-- Both the strong rank bound and the known-simple hypothesis pass to this
specific join inside the actual involution centralizer. -/
theorem orbit_join_sqtk (d : CentralizerData T D s) {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G))) :
    IsSQTK KnownSimple.IsKnownSimple
      (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) :=
  (IsSQTK.equiv (subgroupOfEquivOfLe (orbit_join_le_centralizer d hI))).mp
    ((D.simpleQTKE.involution_centralizer_sqtk d.order).subgroup _)

/-- The source involution, with its literal embedding, forces every Sylow
overgroup in Y to have even order. -/
theorem parabolic_even (d : CentralizerData T D s) {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) {P : Subgroup Y}
    (hSP : ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) ≤ P) :
    ¬ Odd (Nat.card P) := by
  let z : Y := ⟨d.first * d.second, hTY d.central.1⟩
  have hzS : z ∈ (T.subtype hTY : Sylow 2 Y) := d.central.1
  have hd : 2 ∣ Nat.card P := by
    have hh := orderOf_dvd_natCard (⟨z, hSP hzS⟩ : P)
    simpa only [z, Subgroup.orderOf_mk, d.order] using hh
  exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hd)

/-- An attained rank-one E-generation bound gives exactly n(P)=1 on the
original parabolic carrier, including its entire solvable kernel. -/
theorem parabolic_parameter_one (d : CentralizerData T D s) {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) {P : Subgroup Y}
    (hSP : ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) ≤ P)
    (hgen : IsEGenerated 1 P) : generationParameter P = 1 := by
  have hpos := (generationParameter_spec (parabolic_even d hTY hSP)
    ⟨1, by decide, hgen⟩).1
  have hle := generationParameter_le (by decide : 0 < 1) hgen
  omega

/-- The very same family supplied by a model calculation has the exact
numeric parameters required by `NonBenderGenerationAt`. -/
theorem family_parameters_one (d : CentralizerData T D s) {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (Δ : Set (Subgroup Y))
    (hΔ : ∀ P ∈ Δ, ChapterB.IsMinimalParabolicOver (T.subtype hTY) P ∧
      IsEGenerated 1 P) :
    ∀ P ∈ Δ, ChapterB.IsMinimalParabolicOver (T.subtype hTY) P ∧
      generationParameter P = 1 := by
  intro P hP
  exact ⟨(hΔ P hP).1,
    parabolic_parameter_one d hTY (hΔ P hP).1.1.1.le (hΔ P hP).2⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
