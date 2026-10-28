module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaOrder
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleAlphaCard

/-!
# The comparison H-star field is determined by the original alpha subgroup

Both local configurations contain the same Sylow and hence the same Thompson
alpha subgroup. Their fixed centers vanish. E.2.3 therefore makes the single
H-star field have order q², and the paired H-star field have order q, where
q is the order of the original component field. This retains the selected
actions and quotient maps and assumes no generation-parameter equality.
Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

theorem Context.hstar_linear_field_alternatives
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).normal
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let σ := α.comp Y.subtype
    letI := offenderSubgroup_normal α
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        ∃ K : BinaryField, Nat.card K.Carrier = Nat.card F ^ 2 ∧ IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) K 2) ∨
      ∃ (d : SourceTwoFactorCase σ) (K : BinaryField),
        Nat.card K.Carrier = Nat.card F ∧ Nonempty (d.MarkedProduct (linearNatural K 2)) ∧
        ∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hP := source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large
  have hJ := ctx.hstar_thompson_moves_omega_orbit D n hn hF e
  have hzS := RankOneBaumann.sylow_subtype_residual_centralizer_eq_bot_of_omega ctx.hstar.1.1.2
    (ctx.fixed_centers_of_natural_marking D n hn hF e mark hBR).2
  have hα : Nat.card (thompsonAlpha (S : Subgroup H)) = Nat.card F ^ 2 :=
    (RankOneBaumann.alpha_card_subtype ctx.hstar.1.1.2).trans
      (ctx.original_alpha_card D n hn hF e mark hBR)
  rcases ctx.hstar_linear_alternatives_of_seed_centralizer D n hn hF e
      (ctx.seed_centralizer_eq_sylow D n hn hF e mark hBR) with
    ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
  · refine Or.inl ⟨hqs,c,K,?_,hlinear⟩
    exact (quasisimple_linear_alpha_card_of_trivial_sylow_residual_centralizer
      S hP U hU hJ q hq hk hqs c.sectionData K hlinear hzS).symm.trans hα
  · refine Or.inr ⟨d,K,?_,⟨c⟩,hexchange⟩
    have hcard := RankOneBaumann.PairedFactorOrbit.source_alpha_card_of_trivial_sylow_residual_centralizer
      S hP U hU hJ q hq hk d K c hexchange hzS
    rw [hα] at hcard
    nlinarith

end CFSG.Quasithin.Chapter10.MovingHall
