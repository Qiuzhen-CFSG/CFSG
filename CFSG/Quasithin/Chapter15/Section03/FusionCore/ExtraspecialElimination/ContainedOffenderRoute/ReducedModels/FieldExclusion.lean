module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.FieldPreparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Orbit
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.ClassifiedSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.SeedSplitting
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.LateActor
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.Splitting

/-!
# Excluding larger defining fields in the contained-offender route

After containment, the orbit argument identifies the actual component closure
with `L` and gives `H = L ⊔ T`.  The four concrete larger-field carriers can
then be treated as a commuting family with one member: the relative normality
of `L` makes every `T`-conjugate equal to `L`.  The intrinsic cubic Sylow
control and the proved model normalizer calculations force an `SL₂(F)` actor,
and the cubic element forces the degree of `F` to be even.

Natural-module selection remains an explicit unproved premise of this module.
`NaturalSectionSource` is the older, stronger interface requiring a prescribed
actor marking. The weaker `no_larger_field_of_natural_sections` needs only
existence of compatible coordinates and proves their Borel marking. Neither
interface is itself the universal B.5.1 theorem. Its full enumerated conclusion
on the late actor must still be used to construct the natural section.

The splitting is obtained from the universal B.2.14 clause and the 15.3.48(2)
seed conditions. The characteristic-two condition on H/Z is proved from the
literal SectionAction. The older `no_larger_field` signature is preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144;
B.2.13–14, p.78; B.4.2, p.86; B.5.1 and B.5.5–6, pp.99–105.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels

universe u
variable {G : Type u} [Group G] [Finite G]

namespace Input

variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)

include d

/-- An explicit intermediate natural-section premise, not the B.5.1 theorem.
Its prescribed actor marking is stronger than the existence consumed below. -/
abbrev NaturalSectionSource : Prop :=
  ∀ {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (e : starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F),
    2 < Nat.card F →
    ∃ s : Representation.SL2CubicFixedSection.NaturalComponentSection
        (F := F) d.placed.action.representation (starImage H (localSpan L T))
          (componentSection Z H ZS L T),
      s.model = e

omit [Finite G] [IsElementaryAbelian 2 (localSpan ZS H)] d in
private theorem transport_lie_model {D E : Type u} [Group D] [Group E]
    (f : D ≃* E) {e : ℕ} (h : BorelInner.LieComponentModel D e) :
    BorelInner.LieComponentModel E e := by
  cases h with
  | linear_two he F hF m => exact .linear_two he F hF (m.map (f.symm.trans ·))
  | linear_three he F hF m => exact .linear_three he F hF (m.map (f.symm.trans ·))
  | symplectic he F hF m => exact .symplectic he F hF (m.map (f.symm.trans ·))
  | g2 he F hF m => exact .g2 he F hF (m.map (f.symm.trans ·))
  | binary_linear he n hn m => exact .binary_linear he n hn (m.map (f.symm.trans ·))

omit [Finite G] [IsElementaryAbelian 2 (localSpan ZS H)] d in
private theorem top_four_models {D : Type u} [Group D] {F : Type} [Field F]
    (h : FourModels D F) : FourModels (⊤ : Subgroup D) F := by
  rcases h with h | h | h | h
  · exact Or.inl ⟨(Subgroup.topEquiv (G := D)).trans h.some⟩
  · exact Or.inr (Or.inl ⟨(Subgroup.topEquiv (G := D)).trans h.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(Subgroup.topEquiv (G := D)).trans h.some⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(Subgroup.topEquiv (G := D)).trans h.some⟩))

/-- The actual larger-field closure is SL₂ over a field of the same size.
This rank reduction uses no natural-module or splitting hypothesis. -/
theorem larger_field_rank_one
    (orbits : BinaryModels.OrbitClosure.EarlierOrbitAlternative κ)
    (hcontainment : Y0 ≤ localSpan L T)
    {e : ℕ} (he : 1 < e)
    (hmodel : BorelInner.LieComponentModel (L ⧸ pCore 2 L) e) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ e ∧
        Nonempty (starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨hclosed, _, hgen, hnormal, hnormalized, _, _⟩ :=
    d.reduced_structure orbits hcontainment
  have hcomp : (L ⧸ pCore 2 L) ≃* starImage H L :=
    componentStarEquiv H L d.l_le d.component_in_H
  have hmodelL : BorelInner.LieComponentModel (starImage H L) e :=
    transport_lie_model hcomp hmodel
  have hmodelD : BorelInner.LieComponentModel (starImage H (localSpan L T)) e := by
    rw [hclosed]
    exact hmodelL
  obtain ⟨F, hF, hfinite, hchar, hcard, hfour⟩ :=
    four_models_of_lie hmodelD he
  let _ := hF
  let _ := hfinite
  let _ := hchar
  let C := (starImage H Y0).subgroupOf (starImage H (localSpan L T))
  have hC := cubicSylowControl_star H M L Y0 T d.replacement
    d.component.commutator_eq d.normalizes d.sylowIn d.placed.t_le_m
    d.placed.theta_eq d.placed.normalizer_eq d.quotient_card hcontainment
  let K : Unit → Subgroup (starImage H (localSpan L T)) := fun _ => ⊤
  have hKgen : iSup K = ⊤ := by simp [K]
  have hKcomm : Pairwise fun i j => K i ≤ centralizer (K j : Set _) := by
    intro i j hij
    exact (hij rfl).elim
  have hmodels : ∀ i, FourModels (K i) F := by
    intro i
    simpa only [K] using (top_four_models hfour)
  obtain ⟨_, heq⟩ := collapse_of_four_models K hKcomm hKgen e hcard he hmodels C hC
  exact ⟨F, hF, hfinite, hchar, hcard, heq⟩

/-- The field contradiction from an as-yet separately constructed natural
section. The universal B.2.14 input and the seed placement/centrality from
15.3.48(2) supply the decomposition; compatible Borel marking is proved. -/
theorem no_larger_field_of_natural_sections
    (orbits : BinaryModels.OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T)
    (h48 : ⁅ZS, T⁆ ≤ Z)
    (natural : ∀ {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F],
      (starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
      2 < Nat.card F →
      Nonempty (Representation.SL2CubicFixedSection.NaturalComponentSection
        (F := F) d.placed.action.representation (starImage H (localSpan L T))
          (componentSection Z H ZS L T)))
    (hcontainment : Y0 ≤ localSpan L T) :
    ModelSieve.NoLargerField (L ⧸ pCore 2 L) := by
  intro e he hmodel
  obtain ⟨F, hF, hfinite, hcharF, hcard, heq⟩ :=
    d.larger_field_rank_one orbits hcontainment he hmodel
  obtain ⟨eD⟩ := heq
  let _ := hF
  let _ := hfinite
  let _ := hcharF
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hq : 2 < Nat.card F := by
    rw [hcard]
    calc
      2 = 2 ^ 1 := by norm_num
      _ < 2 ^ e := Nat.pow_lt_pow_right (by decide) he
  have hsplit := d.component_section_split hB214 hcontainment hZST h48
  obtain ⟨s⟩ := natural (F := F) eD hq
  have hB' : ∀ e' : starImage H (localSpan L T) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ y : starImage H Y0,
        g * e' ⟨y, (map_mono (comap_mono hcontainment)) y.property⟩ * g⁻¹ ∈
          Matrix.SpecialLinearGroup.rankOneBorel F := by
    intro e'
    exact every_equiv_borel_marking H L Y0 T d.replacement
      d.component.commutator_eq d.normalizes d.sylowIn d.quotient_card
      hcontainment hq e'
  obtain ⟨s', hs'⟩ := NaturalCoordinates.exists_borel_marking
    (map_mono (comap_mono hcontainment)) s hB'
  exact d.no_natural_component_section
    (hZST.trans (isSylowIn_iff.mp d.sylowIn |>.2.1)) hcontainment hsplit s' hs'

set_option linter.unusedVariables false in
/-- Compatibility wrapper for the original stronger conditional interface.
The characteristic-two premise on H and equality with a prescribed marking
are not needed by the weaker theorem. Natural-section existence remains
an intermediate obligation, not a proved appendix application. -/
theorem no_larger_field
    (orbits : BinaryModels.OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hchar : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hZST : ZS ≤ T)
    (h48 : ⁅ZS, T⁆ ≤ Z)
    (natural : NaturalSectionSource d)
    (hcontainment : Y0 ≤ localSpan L T) :
    ModelSieve.NoLargerField (L ⧸ pCore 2 L) := by
  exact d.no_larger_field_of_natural_sections orbits hB214 hZST h48
    (fun e hq => ⟨(natural e hq).choose⟩) hcontainment

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
