module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup

/-!
# Assembly of the nonnormal-fusion degree-twelve action

The local-geometry and eleven-subgroup modules expose separate source
contracts.  Once the fusion eight is known to be nonnormal, the former gives
the selected intersection and the two ambient order alternatives.  Feeding
that record to the latter gives the actual subgroup pair `L ≤ M`; the coset
construction then supplies the faithful sharply five-transitive action on
`Fin 12`.

This is the source-facing conditional contract.  It does not identify the
resulting action with a concrete Mathieu carrier; that comparison belongs to
the subsequent recognition module.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Sections 2 and 4, especially Lemmas 4.3–4.11.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Construct the faithful sharply five-transitive degree-twelve action from
the explicit nonnormal-fusion source hypotheses. -/
public theorem nonempty_action_of_nonnormal_fusion
    (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (hnon : ¬ (fusionCore z).Normal) :
    Nonempty (DegreeTwelveAction G) := by
  obtain ⟨a⟩ := nonempty_sourceGeometry_of_nonnormal_fusion h hn d hnon
  obtain ⟨b⟩ := ElevenSubgroup.nonempty_elevenSubgroupData h hn d a
  exact nonempty_action_of_sourceGeometry h a b

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
