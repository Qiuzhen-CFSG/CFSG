module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Construction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Geometry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Transport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Inputs
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.OrdinaryGeometry

/-!
# The nonsplit exceptional endgame: proved endpoint assemblies

The SL₂ factor case gives B.5.6(5) on the original moved space, via the
literal fixed-quotient comparisons in Transport. This case needs no
additional nonsplitting or cohomology assumption.

For the exceptional second four-space, a fixed supplement supplies the
choice of u fixed by G₂. Construction gives the first faithful indecomposable
four-space; the quotient comparisons give both actual summands in V/C_V(G).
The resulting B.5.6(3) conclusion retains all B.4.8(3) data on both factors.

The higher leaf NonsplitCase.Assembly proves adequate_of_nonsplit by combining
these consumers with Ordinary and ExceptionalSplitting.Source. Those branches
discharge the cohomology, binary moved-action and fixed-supplement obligations
using genuine B.4.8(4). The only earlier-source input of the consumers in this
module is the full EarlierB48Three, owned by qt-b-04-natural-extensions.

The ordinary fixed-supplement case is also proved, retaining possible
central intersections of the second moved space. The remaining ordinary
cohomology problem may consequently assume C_V(G₂)+V₂ is proper; that
assumption must be obtained by the case split here, not inferred from
failure of SplitAtSecond.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of B.5.6, printed p.110, source text lines 5733–5744.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open ComponentReduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The actual hyperplane consumer for every natural linear-two factor. -/
theorem hyperplane_of_linearTwo_factor (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤) (F : BinaryField)
    (hn : IsLinearNatural (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
      (⊤ : Subgroup (second c)).subtype) F 2) : AdequateAlternative ρ := by
  exact adequate_of_second_action c he (second_supplement_of_moved_factor c he f hm)
    (linearTwo_secondCase c he f hm F hn)

/-- Construct both quotient summands after the second fixed supplement is
proved. ExceptionalSplitting.Source supplies it using genuine B.4.8(4). -/
theorem adequate_of_exceptional_fixed_supplement [Finite G]
    [FiniteDimensional (ZMod 2) V] (h48 : EarlierB48Three.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource
      (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
        (⊤ : Subgroup (second c)).subtype))
    (hs : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤) :
    AdequateAlternative ρ := by
  obtain ⟨x,hxf,hx⟩ := exists_outside_in_supplement c he _ hs
  have hd : ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants := by
    intro b
    rw [show ρ (b : G) x = x from hxf b,sub_self]
    exact ρ.invariants.zero_mem
  have hx' : x ∉ c.sectionData.space.toSubmodule ⊔ fixedSpace ρ c.first := by
    simpa only [c.productConfiguration.fixed_eq] using hx
  obtain ⟨q₁⟩ := chosenModule_source h48 c.sectionData.space (first_moved c he) he hx'
  obtain ⟨q₁'⟩ := four_source_transport h48 (actionSymm (firstSaturatedEquiv c he x hx hd)) q₁
  obtain ⟨q₂⟩ := four_source_transport h48 (actionSymm (factorQuotientEquiv c f)) q
  refine Or.inr (.twoFactors {
    first := c.first
    second := second c
    product := c.productConfiguration.product
    firstSpace := saturatedModule c he x hd
    secondSpace := c.productConfiguration.fixed
    decomposition := saturated_quotient_isCompl c he x hx hd
    firstCase := .exceptional ?_ q₁'
    secondCase := .exceptional (second_moved_le_fixed c he) q₂ })
  rw [first_moved c he]
  exact le_sup_left.trans le_sup_left

/-- Every supplied factor action gives the actual two-factor conclusion
when the second fixed space supplements V₂. This closes that case before
the remaining nonsplit cohomology comparison. -/
theorem adequate_of_fixed_second_supplement [Finite G]
    [FiniteDimensional (ZMod 2) V] (h48 : EarlierB48Three.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hs : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤) :
    AdequateAlternative ρ := by
  cases factor_cases c f with
  | inl hf => exact adequate_of_ordinary_fixed_supplement h48 c he f hf hs
  | inr hq =>
    obtain ⟨q⟩ := hq
    exact adequate_of_exceptional_fixed_supplement h48 c he f q hs

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
