module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Enumeration

/-!
# The order-five inputs to the inner HS calculation

The two involutions are the actual degree-100 carrier representatives, with
centralizers of core/S₅ and product type respectively. The module input
concerns cyclic groups of order five on the original vector space. The group
input asks for an element of order five in the literal subgroup generated
by centralizer conjugates of a rank-four elementary actor. In particular it
does not replace the nonsplit core/S₅ extension by an A₅ complement.

These are explicit remaining inputs, not assertions of their existence.
Their consumer is `SourceTwenty.Inner`, following Guralnick--Malle,
*Classification of 2F-modules, I*, Proposition 5.1, HS paragraph, preprint
pp.16--17, and Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner
open Subgroup Representation.BinaryOffender
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims

/-- GM's 2A representative, whose centralizer has the normal core of order 64. -/
abbrev coreInvolution : HS := _root_.Sporadic.LeechRelated.HS.EvenLocalCandidates.e0

/-- GM's 2B representative, with centralizer C₂ × Aut(A₆). -/
abbrev productInvolution : HS := HSInner.ClassCoverage.t

/-- The cyclic restrictions and inverted elements used in the source.
The fixed-point-free five-element is selected on the literal representation;
no assertion about a single matrix model replaces this requirement. -/
structure FiveRestrictions {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) HS V) : Prop where
  order_five : ∀ x : HS, orderOf x = 5 → 16 ≤ fixedCodim σ (zpowers x)
  core_inverts : ∃ x : HS, orderOf x = 5 ∧
    coreInvolution * x * coreInvolution⁻¹ = x⁻¹
  product_inverts_free : ∃ x : HS, orderOf x = 5 ∧
    productInvolution * x * productInvolution⁻¹ = x⁻¹ ∧
    fixedSpace σ (zpowers x) = ⊥

/-- The normal-closure consequence of the actual core/S₅ centralizer.
Normality is only inside the indicated centralizer. The order-five element
lies in its actual preimage, not in an assumed complement to the core. -/
def CoreClosureFive : Prop :=
  ∀ A : Subgroup HS, IsElementaryTwo A → rank A = 4 →
    ∀ t ∈ A, IsConj coreInvolution t →
      ∃ x ∈ centralizerConjugateClosure A t, orderOf x = 5

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner
