module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointFusion
public import CFSG.Quasithin.Chapter12.Section09.SourceInputs
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.LargerLinearInput
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard

/-!
# Source inputs for the escaping configuration in 12.5.1

This file names the actual data used by the last paragraph of the proof.  The
data are independent conclusions of the local, weak-closure, fusion and
corank arguments; none is folded into `Hypothesis1223`.  In particular, `H`
is an original `HStar` member, `K` is the embedded two-residual `O²(H)`, and
`A` is the literal conjugate of the chosen module.

Source: Aschbacher--Smith, proof of 12.5.1, printed pp.821--822 (PDF p.839),
together with G.2.2 and E.3.6.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/- The G.2.1 setup used for `H₁ = L₁H` and `U_H = ⟨V₇ᴴ⟩`. -/
def escapingH₁ (s : SylowExteriorMarking D) (H : Subgroup G) : Subgroup G :=
  s.marking.Li 1 ⊔ H

def escapingSetup (s : SylowExteriorMarking D) (H : Subgroup G) :
    ChapterG.Section02.Setup G :=
  { V := s.marking.Vi 7
    V₁ := s.marking.Vi 1
    L := s.marking.Li 1
    T := T
    H := escapingH₁ s H }

namespace SylowExteriorMarking

variable (s : SylowExteriorMarking D)

/-- The source conclusions consumed by the terminal construction.  The
quotient/model and supplement fields retain the literal objects from p.822;
the remaining fields are the exact local identities used below. -/
structure EscapingSource (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) where
  H : Subgroup G
  hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M
  H_le_G₁ : H ≤ s.marking.Gi 1
  K : Subgroup G
  K_eq : K = (pResidual 2 H).map H.subtype
  K_model : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4
  K_not_le_M : ¬ K ≤ s.marking.M
  X : Subgroup G
  H_le_XT : H ≤ X ⊔ (T : Subgroup G)
  X_not_le_M : ¬ X ≤ s.marking.M
  g2 : (escapingSetup s H).Hypothesis
  span_eq : (escapingSetup s H).U = s.marking.UH H
  /-- The original weak-closure subgroup `W₀` and its normalizer bound. -/
  W₀ : Subgroup G
  W₀_centralizes_V : W₀ ≤ centralizer (V : Set G)
  W₀_normalizer_le_M : normalizer (W₀ : Set G) ≤ s.marking.M
  g : G
  A_le_W₀ : V.map (MulAut.conj g).toMonoidHom ≤ W₀
  A_le_T : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)
  A_le_H : V.map (MulAut.conj g).toMonoidHom ≤ H
  escapes_core : ¬ V.map (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2
  span_normalizes : s.marking.UH H ≤
    normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)
  commutator_line : ⁅s.marking.UH H,
      V.map (MulAut.conj g).toMonoidHom ⊓ (s.marking.Li 1 ⊔ H).pCoreIn 2⁆ ≤
    s.marking.Vi 1
  corank_le_two : ChapterE.subgroupCorank
      (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ (s.marking.Li 1 ⊔ H).pCoreIn 2) ≤ 2
  corank_lt_globalS :
    let := D.elementary
    let := IsElementaryAbelian.map (p := 2) (A := V)
      (MulAut.conj g).toMonoidHom
    (ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓
        (s.marking.Li 1 ⊔ H).pCoreIn 2) : ℕ∞) <
      ChapterE.globalS (V.map (MulAut.conj g).toMonoidHom)
  /-- The rank estimate `r(G,V)>3=s(G,V)` used to promote the action to `A`. -/
  rank_gt_three :
    let := D.elementary
    let := IsElementaryAbelian.map (p := 2) (A := V)
      (MulAut.conj g).toMonoidHom
    (3 : ℕ∞) < ChapterE.globalS (V.map (MulAut.conj g).toMonoidHom)
  faithful_action_kernel : H ⊓ centralizer (s.marking.UH H : Set G) ≤
    (s.marking.Li 1 ⊔ H).pCoreIn 2

/-- The conjugate selected in the source paragraph.  This is kept separate
from the target record so the literal map, rather than an existentially
chosen subgroup, is visible to downstream consumers. -/
def escapingA {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) : Subgroup G :=
  V.map (MulAut.conj e.g).toMonoidHom

/-- The `Q_H = O₂(H₁)` appearing in the quotient action. -/
def escapingQ {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) : Subgroup G :=
  (escapingH₁ s e.H).pCoreIn 2

/-- The literal `B = A ∩ Q_H` used in E.3.6. -/
def escapingB {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) : Subgroup G :=
  escapingA s e ⊓ escapingQ s e

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
