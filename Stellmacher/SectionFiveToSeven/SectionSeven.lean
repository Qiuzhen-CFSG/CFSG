module

public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.CosetGraphConstruction
public import Stellmacher.SectionFiveToSeven.CriticalPathExistence
public import Stellmacher.SectionFiveToSeven.Result7_1
public import Stellmacher.SectionFiveToSeven.Result7_2
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_4
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.SectionFiveToSeven.Result7_7
public import Stellmacher.SectionFiveToSeven.Result7_8
public import Stellmacher.SectionFiveToSeven.Result7_8.QuotientConfiguration
public import Stellmacher.SectionFiveToSeven.Result7_8.PrescribedActorConfiguration
public import Stellmacher.SectionFiveToSeven.Result7_8.InvolutionConfiguration

/-!
# Stellmacher Section 7 assembly

This module re-exports the numbered Section 7 results and their shared
Hypothesis 2 bridge, together with the finite generated-pair coset-graph
constructor and initial normalized critical-path existence. It also exports
the proved quotient-action portion of
(7.8), whose explicit quotient-involution and fixed-neighbor-core conclusions
remain separate from the stronger source-facing numbered theorem, together
with its actual-involution specialization for exponent-two actors. The
prescribed-actor configuration retains an actor chosen before extraction,
outside the same index-two coatom, for the application in (8.6).
-/
