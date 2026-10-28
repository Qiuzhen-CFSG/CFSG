module
public import Stellmacher.SectionEight.EightFourSmallRankAction
public import Stellmacher.SectionEight.EightFourSourceNineFixedCardTransport

/-!
# The two-factor rank conclusion in Stellmacher (8.4)

The actual source-nine edge-fixed index transports to the original quotient
action as `|Fix(J)| = 2 |Fix(Sylow)|`. The action reduction proves all remaining
Section One inputs, including the strict module bound greater than four.
Consequently the original initial center has order sixteen and the canonical
one-seven family for the supplied witness action has exactly two factors.
The original ambient J-fixed subgroup has order four.

The local theorems use the same graph and supplied quotient action. Canonical
statements are retained through the local-context and configuration adapters.
Every hypothesis of the actor-index theorem is retained. No rank or order
bound, replacement witness, or descent of Hypothesis Two is assumed.
Source: Stellmacher, Journal of Algebra 190 (1997), printed p.40/PDF p.30,
(8.4), immediately after the actor-index-two calculation.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

section LocalProof

variable {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

public theorem eight_four_source_nine_small_rank_local :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 16 ∧
      (SectionOne.oneSevenFactors (G := w.X)
        (V := ZAt ctx.Γ ctx.criticalPath.a)).card = 2 := by
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  have hdata := eight_four_small_rank_of_fixed_card_double_local ctx hcenter w
    (eight_four_source_nine_fixed_card_transport_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen)
  exact ⟨hdata.1, hdata.2.1⟩

public theorem eight_four_source_nine_fixed_card_four_local :
    Nat.card (w.oneJFixedPoints S) = 4 := by
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  exact (eight_four_small_rank_of_fixed_card_double_local ctx hcenter w
    (eight_four_source_nine_fixed_card_transport_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen)).2.2

public theorem eight_four_source_nine_shifted_fixed_card_four_local :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    Nat.card (F next configuration.d) = 4 := by
  classical
  let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
  have hindex := eight_four_source_nine_fixed_center_index_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hnonzero : F next configuration.d ≠ ⊥ := by
    intro hzero
    change (ZAt ctx.Γ configuration.d).relIndex (F next configuration.d) = 2 at hindex
    rw [hzero, Subgroup.relIndex_bot_right] at hindex
    contradiction
  obtain ⟨actor, horient⟩ : ∃ actor : H,
      ctx.Γ.act actor ctx.criticalPath.a = next ∧
      ctx.Γ.act actor ctx.criticalPath.firstStep = configuration.d := by
    by_contra hnone
    apply hnonzero
    rw [hformula next configuration.d]
    apply le_bot_iff.mp
    exact iSup_le fun actor => iSup_le fun horient => (hnone ⟨actor, horient⟩).elim
  have hconj := hcov actor ctx.criticalPath.a ctx.criticalPath.firstStep
  rw [horient.1, horient.2, hbase] at hconj
  change Nat.card (F next configuration.d) = 4
  rw [hconj]
  calc
    _ = Nat.card (w.oneJFixedPoints S) :=
      Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective
    _ = 4 := eight_four_source_nine_fixed_card_four_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen

end LocalProof

section CanonicalProof

variable {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

public theorem eight_four_source_nine_small_rank :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 16 ∧
      (SectionOne.oneSevenFactors (G := w.X)
        (V := ZAt ctx.Γ ctx.criticalPath.a)).card = 2 := by
  exact eight_four_source_nine_small_rank_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_fixed_card_four :
    Nat.card (w.oneJFixedPoints S) = 4 := by
  exact eight_four_source_nine_fixed_card_four_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_shifted_fixed_card_four :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    Nat.card (F next configuration.d) = 4 := by
  exact eight_four_source_nine_shifted_fixed_card_four_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

end CanonicalProof

end Stellmacher.SectionEight
