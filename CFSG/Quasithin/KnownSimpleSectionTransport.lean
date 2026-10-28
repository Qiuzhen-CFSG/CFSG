module
public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Known-simple section transport across universes

A simple quotient in the target universe is represented by the literal
kernel quotient of its source preimage. That quotient lies in the source
universe, where the K-group hypothesis applies. Cross-universe invariance
of the complete known-simple catalogue then returns the original simple
section. Odd prime ranks transport through the inverse group equivalence.

This permits a native finite group to use its actual small permutation image
without weakening the K-group hypothesis or changing the model carrier.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin
/-- Transport the full known-simple SQTK hypothesis across an equivalence,
including between different universes. -/
theorem IsSQTK.knownSimple_of_equiv {G : Type*} {H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (h : IsSQTK KnownSimple.IsKnownSimple G) :
    IsSQTK KnownSimple.IsKnownSimple H := by
  refine ⟨?_,?_⟩
  · intro p hp ho
    exact (Theory.GroupTheory.primeRank_le_of_injective p e.symm.toMonoidHom e.symm.injective).trans
      (h.stronglyQuasithin p hp ho)
  · intro S _ hs U f hf
    let V := U.comap e.toMonoidHom
    let g : V →* S := f.comp (e.toMonoidHom.subgroupComap U)
    have hg : Function.Surjective g := hf.comp
      (e.toMonoidHom.subgroupComap_surjective_of_surjective U e.surjective)
    let j := QuotientGroup.quotientKerEquivOfSurjective g hg
    let : IsSimpleGroup S := hs
    have ht := h.isKGroup (V ⧸ g.ker) j.isSimpleGroup V
      (QuotientGroup.mk' g.ker) (QuotientGroup.mk'_surjective g.ker)
    exact ht.of_mulEquiv j.symm
end CFSG.Quasithin
