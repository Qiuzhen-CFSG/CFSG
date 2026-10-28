module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Mathieu
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Local
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.Mathieu.InnerPlacement

/-!
# Placement and Sylow markings for the selected Mathieu residuals

The transport R = T_C^g and the earlier tight-normalizer isomorphism
R ≃ C_{T_C}(R) force T_C to centralize R by equality of finite orders.
This uses the actual transport already in `ResidualInputs`.

Inverse conjugation gives an actual isomorphism between the two selected
residuals. The checked Mathieu row comparisons then show that their actors
have the same two-central marking in N_G(L)/C_G(L). The M₁₂, M₂₂ and M₂₄
source tables remain explicit prerequisites; M₁₁ and M₂₃ use their proved
tables. Every normalizer action and central covering kernel is retained.
`InnerPlacement` separately proves Δ₀ membership and lifts the inverse
inner action for M₁₁, M₂₃ and M₂₄.

These reductions do not construct `OddRankThreeWitness`: the ambient
nontrivial two-subgroup and three independent commuting odd-prime directions
are still required. In particular equal markings and isomorphic residuals
are not equality of the embedded residuals. No normalization of the chosen
conjugator, residual invariance, or replacement conjugator is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(3)–(7), printed p.1171; 16.4.2(1),(4), p.1183;
16.4.11(1),(3), pp.1193–1194; and 16.5.5–6, p.1197.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16
open CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic
open Centrality.OtherRows

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Transport and the earlier tight-normalizer isomorphism give [T_C,R] = 1. -/
theorem selected_commutingSylow_centralizes (d : ResidualInputs T z L g R) :
    commutingSylow T L ≤ centralizer (R : Set G) := by
  obtain ⟨f⟩ := d.setup.normalizer_structure.2.1
  have hc : Nat.card R = Nat.card (commutingSylow T L) := by
    rw [d.transport]
    exact card_map_of_injective (MulAut.conj g).injective
  have he : commutingSylow T L ⊓ centralizer (R : Set G) = commutingSylow T L :=
    eq_of_le_of_card_ge inf_le_left (by
      rw [← hc]
      exact (Nat.card_congr f.toEquiv).le)
  exact inf_eq_left.mp he

/-- The actual inverse and forward actors have the same Sylow marking,
conditional on the three remaining exact source tables. This does not assert
that their embedded residuals coincide or produce an ambient rank witness. -/
theorem mathieu_selected_marking_of_tables
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R)
    (name : ClassificationModels.SporadicName) (hn : IsMathieuName name)
    (e : L ⧸ center L ≃* name.Carrier)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    (m12 : ∀ a : MulAut _root_.Sporadic.Mathieu.M12,
      orderOf a = 2 → M12InvolutionAlternative a)
    (m22 : ∀ a : MulAut _root_.Sporadic.Mathieu.M22,
      orderOf a = 2 → M22InvolutionAlternative a)
    (m24 : ∀ a : MulAut _root_.Sporadic.Mathieu.M24,
      orderOf a = 2 → M24InvolutionAlternative a) :
    let u : normalizer (L : Set G) := ⟨MulAut.conj g z,
      d.setup.sylow_normalizes (d.setup.le_sylow (forward_actor d.setup d.transport).1)⟩
    let v : normalizer (L : Set G) := ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v) := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  dsimp only
  let u : normalizer (L : Set G) := ⟨MulAut.conj g z,
    d.setup.sylow_normalizes (d.setup.le_sylow (forward_actor d.setup d.transport).1)⟩
  let v : normalizer (L : Set G) := ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩
  have hu : orderOf (actionMap (L := L) le_rfl u) = 2 :=
    (actionMap_orderOf (d.setup.le_sylow.trans d.setup.sylow_normalizes)
      d.setup.normalizer_structure.2.2.2
      ⟨MulAut.conj g z, (forward_actor d.setup d.transport).1⟩).trans
        (forward_actor d.setup d.transport).2
  have hv : orderOf (actionMap (L := L) le_rfl v) = 2 :=
    (action_order v).symm.trans (d.inverse_action_order hne)
  have hodd : pPrimeCore 2 L = ⊥ := by
    have hc := Subgroup.IsSubnormal.pPrimeCore_eq_bot
      (hG.evenType.oddCore z d.setup.involution)
      (L.subgroupOf (involutionCentralizer z)) d.setup.component.2.1
    have hm := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe d.setup.component.1)
    simpa only [hc, Subgroup.map_bot] using hm.symm
  let f : modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val :=
    ((MulAut.conj g⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr d.inverse_transport)
  have separate (a b : normalizer (L : Set G))
      (ha : orderOf (actionMap (L := L) le_rfl a) = 2)
      (hb : orderOf (actionMap (L := L) le_rfl b) = 2)
      (hac : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl a))
      (hbc : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl b)) :
      ¬ Nonempty (modifiedCentralizerResidual L a.val ≃*
        modifiedCentralizerResidual L b.val) := by
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact Mathieu.m11_no_equiv e a b hb hbc
    · exact Mathieu.m12_no_equiv hodd e m12 a b ha hb hac hbc
    · exact Mathieu.m22_no_equiv hodd e m22 a b ha hb hac hbc
    · exact Mathieu.m23_no_equiv e a b hb hbc
    · exact Mathieu.m24_no_equiv hodd e m24 a b ha hb hac hbc
  constructor
  · intro hc
    by_contra hn
    exact separate u v hu hv hc hn ⟨f⟩
  · intro hc
    by_contra hn
    exact separate v u hv hu hc hn ⟨f.symm⟩

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic
