module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Transport
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Model.Assembly

/-!
# Assembly boundary for the HS order-eleven fixed-space calculation

`ElevenFixedFree.Transport` proves the conditional passage from one actual
binary model calculation and universal comparison after algebraic closure to
`DegreeTwentyElevenFixedFree`. `Model.Assembly` constructs that faithful
absolutely irreducible binary model on the actual carrier and proves its
order-eleven calculation, with source-inherited simplicity. Universal
representation recognition remains required; this module does not assert
the unconditional `degreeTwentyElevenFixedFree` theorem.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph, author-preprint p.16. The trace-field assembly consumes the
unconditional kernel statement only after these premises are discharged.
-/
