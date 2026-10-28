module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Natural
public import Theory.Representation.HexacodeAction.TerminalIrreducible

/-!
# Source contracts for the alternating branches of Chapter K

The input is the actual faithful binary action with quasisimple F*(G),
irreducible restriction, and cubic ratio at most two. The central quotient
is identified with A₆ or A₇. Recognition must produce intertwiners with
the permutation, four-dimensional A₇, or hexacode models, together with
the permitted ambient extension. An isomorphism of actors in `ActionEquiv`
allows precisely the automorphism twist in source quasiequivalence.

The output retains the corrected B.4.2 offender contract, including F₄
vector planes of dimension two, or both ratios 3/2 for the natural A₇
action. These definitions specify obligations; they do not assert the
representation catalogue or any source classification theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.1–K.1.3,
printed pp.452–453, citing GM02 Theorem 6.2 and Table 6.3.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The standing Chapter K hypotheses, restricted to the two K.1 quotients.
Finiteness of G and finite dimensionality of V are ambient theorem assumptions. -/
structure Input (K : GroupClass.{u}) (L : Subgroup G) : Prop where
  sqtk : IsSQTK K G
  fitting : L = generalizedFitting G
  quasisimple : IsQuasisimple L
  faithful : Function.Injective ρ
  irreducible : IsIrreducible (ρ.comp L.subtype)
  cubic_bound : cubicRatio ρ ≤ 2
  quotient : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))

/-- A natural alternating action and its only permitted ambient extension.
The outer case identifies the actual component inside the full symmetric action. -/
structure NaturalAction (L : Subgroup G) (n : ℕ) where
  restricted : ActionEquiv (ρ.comp L.subtype) (alternatingNatural n)
  extension : L = ⊤ ∨ Nonempty (MarkedActionEquiv ρ ⊤ L
    (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))

/-- K.1.3's actual hexacode action, with the permitted triple-S₆ extension.
Its odd elements are the semilinear operators in that concrete model. -/
structure HexacodeAction (L : Subgroup G) where
  restricted : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction
  extension : L = ⊤ ∨ Nonempty
    (MarkedActionEquiv ρ ⊤ L Hexacode.action Atlas.Codes.hexSign.ker)

/-- The GM02 recognition obligation, including ambient extension restrictions.
The A₇ four-space is the actual restriction along A₇ ↪ A₈ ≃ SL₄(2). -/
inductive RecognizedAction (L : Subgroup G) : Prop
  | six (action : NaturalAction ρ L 6)
  | sevenNatural (action : NaturalAction ρ L 7)
  | sevenFour (whole : L = ⊤)
      (action : ActionEquiv (ρ.comp L.subtype) AlternatingSevenConjugatePair.Model.natural)
  | tripleSix (action : HexacodeAction ρ L)

/-- The complete K.1 conclusion needed by the B.4.2/B.4.5 assembly.
The FF branch keeps all applicable corrected B.4.2 clauses and the actual
model intertwiner. The non-FF branch retains both, distinct, ratios. -/
inductive Conclusion (L : Subgroup G) : Prop
  | ff (recognition : RecognizedAction ρ L)
      (source : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
        ρ L (offenderSubgroup ρ))
  | sevenNatural (whole : L = ⊤)
      (action : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7))
      (quadratic : quadraticRatio ρ = 3 / 2)
      (cubic : cubicRatio ρ = 3 / 2)

end CFSG.Quasithin.ChapterK.Alternating
