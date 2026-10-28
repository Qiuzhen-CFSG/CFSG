module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.DualAction

/-!
# Supplying the faithful action to the extraspecial duality argument

The empty faithful local family and the earlier 15.3.48 conclusions give
faithfulness on U/C_U(Q). Passing this proved input to the existing F.9.7
duality argument shows that both conjugate spans are elementary abelian
once the extraspecial calculation gives Ω₁(Q) ≤ S.

Only the omega bound remains an input from the extraspecial calculation.
Neither span is assumed abelian, and no faithful-action premise is retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(c)–(d), printed p.1143.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

/-- The downstream extraspecial argument receives the proved faithful
action. Its only remaining extraspecial input is the actual omega bound;
commutativity of neither conjugate span is assumed. -/
theorem extraspecial_spans_of_emptyLf_and_omega_bound
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (V A Z S : Subgroup H) [Z.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hAQ : A ≤ pCore 2 H) (hAS : A ≤ centralizer (S : Set H))
    (hOmegaS : omegaOneAmbient (pCore 2 H) ≤ S)
    (hZQ : Z ≤ pCore 2 H) (hZ : Z ≤ center H) (hZcard : Nat.card Z = 2)
    (hZsyl : centralInvolutions (T.subtype hTH) ≤ Z)
    (hPhi : (frattini (localSpan A ⊤)).map (localSpan A ⊤).subtype ≤ Z)
    (hcomm : ⁅pCore 2 H, localSpan A ⊤⁆ ≤ Z)
    (hsmall : centralizerModulo ⊤ (localSpan A ⊤) Z ≤ pCore 2 H)
    (hQV : pCore 2 H ≤ normalizer (V : Set H))
    (hweak : ∀ h : H, V.map (MulAut.conj h).toMonoidHom ≤ normalizer (V : Set H) →
      V.map (MulAut.conj h).toMonoidHom ≤ centralizer (V : Set H)) :
    localSpan A ⊤ ≤ (center (omegaOneAmbient (pCore 2 H))).map
        (omegaOneAmbient (pCore 2 H)).subtype ∧
      IsElementaryAbelian 2 (localSpan A ⊤) ∧
      localSpan V ⊤ ≤ pCore 2 H ∧ IsElementaryAbelian 2 (localSpan V ⊤) := by
  have hQne : pCore 2 H ≠ ⊥ := by
    intro hb
    have hz : Z = ⊥ := le_bot_iff.mp (hZQ.trans hb.le)
    have hzn : Z ≠ ⊥ := (one_lt_card_iff_ne_bot Z).mp (by omega)
    exact hzn hz
  have hUQ : localSpan A ⊤ ≤ pCore 2 H :=
    conjugateSpanBy_le hAQ le_normalizer_of_normal
  exact extraspecial_spans_of_omega_bound V A (pCore 2 H) Z S hAQ hAS hOmegaS
    hZQ hZ hZcard hcomm
    (span_faithful_of_emptyLf T H hTH hQne hc hempty A Z hUQ
      (hPhi.trans hZ) (hZsyl.trans hZ) hsmall) hQV hweak

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

end
