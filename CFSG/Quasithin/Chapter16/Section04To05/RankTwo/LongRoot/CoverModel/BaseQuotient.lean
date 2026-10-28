module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.CoverModel.ActionBounds
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieSpecialRadical
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.Frattini.OmegaProducts

/-!
# The highest-root residual's base sections over four elements

The actual first local group has two-core equal to the five-root radical
omitting root F. The radical's Frattini subgroup equals its center of order
four, so its intrinsic Frattini section has order 256. The existing quotient
map to PSL₂, followed by the five-point action, gives an actual equivalence
of the top quotient with A₅ and hence its seven-free automorphism bound.

This is the center-free base calculation. The covered residual requires a
proved section comparison with this group. Its five-element and natural
module action also remain to be constructed.

Source: Aschbacher–Smith, Lemma 16.5.13, printed p.1202, using the root
group calculations in F.1.11–12, printed pp.262–264. The imported root
formulas retain their ATLAS attribution and license.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.CoverModel
open Subgroup Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The specified PSL₂ quotient followed by PSL₂(4)≃A₅. -/
noncomputable def baseTopEquiv (hF : Nat.card F = 4) :
    (local₁ (F := F) ⧸ pCore 2 (local₁ (F := F))) ≃* alternatingGroup (Fin 5) :=
  local₁CoreQuotientEquivPSL.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some

theorem base_frattini_card (hF : Nat.card F = 4) :
    Nat.card (frattini (pCore 2 (local₁ (F := F)))) = 4 := by
  let e := local₁CoreEquivRadical (F := F)
  rw [Nat.card_congr ((frattini (pCore 2 (local₁ (F := F)))).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv,
    frattini_map_equiv e, radical₁_frattini_eq_center, card_center_radical₁, hF]

theorem base_section_card (hF : Nat.card F = 4) :
    Nat.card (pCore 2 (local₁ (F := F)) ⧸ frattini (pCore 2 (local₁ (F := F)))) = 256 := by
  have h := card_eq_card_quotient_mul_card_subgroup
    (frattini (pCore 2 (local₁ (F := F))))
  rw [card_local₁_pCore, hF, base_frattini_card hF] at h
  omega

/-- Application to every action on the actual base residual. -/
theorem base_top_action_seven_coprime {M : Type*} [Group M]
    (hF : Nat.card F = 4) (a : M →* MulAut (local₁ (F := F))) :
    Nat.Coprime 7 (Nat.card (topAction a).range) :=
  seven_coprime_top_of_equiv a (baseTopEquiv hF)

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.CoverModel
