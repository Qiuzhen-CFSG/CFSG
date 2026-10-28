module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.SourceApplication
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityOddModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsMathieu
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# Sylow-overgroup uniqueness for the F.9.18 component catalogue

Each genuine F.9.18 group model has at most one C-component in every
overgroup of a full Sylow two-subgroup. The center is solvable, so the
central-quotient rows lift to the original quasisimple group. The binary
symplectic and G₂ derived groups use their actual small-parameter
isomorphisms, and the triple Mathieu cover uses its literal central quotient.

This is the A.3.12 uniqueness input used in the original 14.7.32
overcomponent comparison; it places no conclusion about that comparison
among its hypotheses. Source: Aschbacher–Smith, A.3.12, F.9.18 and
14.7.32, printed pp.47–48,325–326,1056, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components
open Chapter1.Section02.MovedMaximality Models
variable {X : Type*} [Group X] [Finite X]

private theorem symplectic_unique [IsSimpleGroup X] [Group.IsPerfect X]
    {n : ℕ} (hn : 1 ≤ n) (hm : IsSp4DerivedAt X (2^n)) :
    SylowOvergroupComponentUnique X := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases hn2 : 2 ≤ n
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact symplectic_even_sylow_overgroup_component_unique hn2
      ⟨F,inferInstance,inferInstance,hF,
        ⟨e.trans ((Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn2).trans
          Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv)⟩⟩
  · have hn1 : n = 1 := by omega
    exact small_alternating_sylow_overgroup_component_unique (Or.inr
      ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (by simpa only [hn1,pow_one] using hF))⟩)

private theorem g2_unique [IsSimpleGroup X] [Group.IsPerfect X]
    {n : ℕ} (hn : 1 ≤ n) (hm : IsG2DerivedAt X (2^n)) :
    SylowOvergroupComponentUnique X := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases hn2 : 2 ≤ n
  · exact g2_even_sylow_overgroup_component_unique hn2
      ⟨F,inferInstance,inferInstance,hF,
        ⟨e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hF)⟩⟩
  · have hn1 : n = 1 := by omega
    exact binary_g2_derived_sylow_overgroup_component_unique
      ⟨e.trans (Atlas.G2.DerivedEvenOrder.derivedFieldEquiv
        (Atlas.G2.binaryFieldEquiv (by simpa only [hn1,pow_one] using hF)))⟩

/-- The actual F.9.18 models have at most one C-component in each full-Sylow overgroup. -/
theorem f918_sylow_overgroup_component_unique [IsQuasisimple X]
    (hm : F918Models X) : SylowOvergroupComponentUnique X := by
  let : Group.IsSolvable (center X) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  rcases hm with ⟨hm,_⟩ | hm | hm
  · apply SylowOvergroupComponentUnique.of_quotient (center X)
    let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
    cases hm with
    | bender hm => exact bender_sylow_overgroup_component_unique hm
    | linear_three n hn hm => exact linear_three_even_sylow_overgroup_component_unique hn hm
    | symplectic n hn hm => exact symplectic_unique hn hm
    | g2 n hn hm => exact g2_unique hn hm
    | linear_four hm => exact binary_higher_linear_sylow_overgroup_component_unique (Or.inl rfl) hm
    | linear_five hm => exact binary_higher_linear_sylow_overgroup_component_unique (Or.inr rfl) hm
    | alternating_seven hm => exact alternating_seven_sylow_overgroup_component_unique hm
  · exact mathieu_twenty_two_sylow_overgroup_component_unique hm
  · apply SylowOvergroupComponentUnique.of_quotient (center X)
    exact mathieu_twenty_two_sylow_overgroup_component_unique hm.2.2
end CFSG.Quasithin.Chapter13.Section08.Components
