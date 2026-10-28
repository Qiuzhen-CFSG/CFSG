module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.FixedImage
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.QuotientSelection
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers

/-!
# The two HS centralizer-layer witnesses

The quotient selection constructs two actors in the actual four-group, and
the cover calculations identify their fixed-subgroup layers as A₈ and A₆.
Faithful conjugation preserves the orders of the selected actors; layer
transport then gives witnesses in the original ambient group.

`Configuration.mixedHSLayers_of_source_clauses` discharges both intrinsic
calculations, retaining only the earlier HS clauses of 16.1.2(2),
16.1.5(10), 16.1.7(3h), and I.2.2(5a) as explicit source inputs.
The conditional API `mixedHSLayers_of_quotient_and_cover` is preserved.
No all-elements component hypothesis is used in either assembly.

Source: Aschbacher–Smith, 16.3.5, printed p.1179 / PDF p.1196;
16.1.2/5/7, printed pp.1170–1173; I.2.2(5a), printed p.409.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
open Subgroup Theory.GroupTheory
open OtherPreliminaries.JankoTwoHigmanSims
universe u
variable {G : Type u} [Group G]

/-- Transport the independently selected quotient rows and proved covering
layers to the literal centralizers in G. The two intrinsic inputs remain
proof obligations, rather than hypotheses of the source theorem. -/
theorem mixedHSLayers_of_quotient_and_cover {E I : Subgroup G}
    (hn : E ≤ normalizer (I : Set G))
    (hf : Function.Injective (inducedAction E I hn))
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hselect : QuotientFixedTypes E I hn e)
    (hcover : CoverLayerIdentification I e) : MixedHSLayers E I := by
  obtain ⟨s, t, hs, ht, hs8, ht6⟩ := hselect
  have hsorder : orderOf (inducedAction E I hn s) = 2 :=
    (orderOf_injective _ hf s).trans hs
  have htorder : orderOf (inducedAction E I hn t) = 2 :=
    (orderOf_injective _ hf t).trans ht
  obtain ⟨e8⟩ := (hcover _ hsorder).1 hs8
  obtain ⟨e6⟩ := (hcover _ htorder).2 ht6
  refine ⟨s, t, s.property, ?_, t.property, ?_,
    ⟨(centralizerLayerEquiv E I hn s).trans e8⟩,
    ⟨(centralizerLayerEquiv E I hn t).trans e6⟩⟩
  · intro he
    have : s = 1 := Subtype.ext he
    simp only [this, orderOf_one] at hs
    omega
  · intro he
    have : t = 1 := Subtype.ext he
    simp only [this, orderOf_one] at ht
    omega

/-- Construct the two actual ambient HS centralizer layers from the
configuration and the earlier source clauses. The quotient rows are selected
inside E and the covering layers are proved before transporting to G;
neither calculation nor the all-elements component hypothesis is assumed. -/
theorem Configuration.mixedHSLayers_of_source_clauses [Finite G]
    {𝒦 : GroupClass.{u}} {E L I : Subgroup G} {a i : G}
    (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (h15 : ∀ r : MulAut Sporadic.LeechRelated.HS.Carrier,
      orderOf r = 2 → HSInvolutionAlternative r)
    (h17 : ∀ r : MulAut Sporadic.LeechRelated.HS.Carrier, orderOf r = 2 →
      ∀ J : Subgroup r.fixedSubgroup, IsComponent r.fixedSubgroup J →
        IsHSCentralizerComponent J)
    (hcard : Nat.card (center I) ≤ 2)
    (hlift : CoverLayers.TwoCentralLifting I e) : MixedHSLayers E I :=
  mixedHSLayers_of_quotient_and_cover h.normalizes h.faithful e
    (h.quotientFixedTypes_of_source_clauses e h15 h17)
    (h.coverLayerIdentification e hcard hlift)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
