module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Transport
public import Theory.SpecificGroups.PSL3Even.FixedComponents
/-!
# Unconditional binary linear-three fixed-component inspection

The concrete involution rows exclude an alternating-six component. Transport
uses the same model equivalence for the actor and its fixed subgroup, so this
supplies the literal `LinearInspection` input to E.6.23 without an additional
small-field marking premise.

Source: Aschbacher–Smith 16.1.4, printed pp.1170–1171, and E.6.23, p.254.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
universe u
/-- The full linear-three input to E.6.23, on its original carrier and actor. -/
theorem linearInspection : LinearInspection.{u} := by
  intro D _ _ _ _ n hn hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩:=hm
  apply ExcludesFixedSix.of_equiv e
  intro a ha S hS hs
  exact Matrix.PSL3Even.FixedComponents.not_alternating_six_component (by omega) hF
    a ha (S.subgroupOf a.fixedSubgroup) hS.2
    (hs.map (fun s=>(subgroupOfEquivOfLe hS.1).trans s))
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
