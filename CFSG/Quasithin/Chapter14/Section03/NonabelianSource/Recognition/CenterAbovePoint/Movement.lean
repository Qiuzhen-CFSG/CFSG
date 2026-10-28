module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Image
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.InverterMovement

/-!
# The displaced point is the marked commutator in the full orthogonal case

W-hat is the actual three-dimensional hyperplane. The residual inverter
inside the displaced center moves a vector in this hyperplane under the
original terminal action. Earlier center geometry bounds its ambient
commutator by the displaced point of order two, so that bound is equality.

Source: Aschbacher--Smith 14.3.15, printed p.995.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {L M : Subgroup G}

theorem rankTwo_full_orthogonal_center_commutator
    (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g∈F.P L) (hgH : g∉F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU≠F.Vi 1)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤)
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) :
    ⁅F.W,conjugate F.ZU g⁆ = conjugate (F.Vi 1) g := by
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,_⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  let form := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hq := F.finrank_quotient_hat_centralizer (by decide) d.seed_center form
  have hdim := (hatSpace F F.W).finrank_quotient_add_finrank
  change finrank (ZMod 2) (Additive F.Uhat ⧸ hatSpace F F.W)=1 at hq
  have hw : 3 ≤ finrank (ZMod 2) (hatSpace F F.W) := by omega
  obtain ⟨_,_,r,hrZ,hr2,hrinv⟩ := rankTwo_full_orthogonal_center_residual h F d hne g hgP hgH hyp hZ hr
  obtain ⟨w,hwW,hwmove⟩ := ChapterG.Section09.FittingRecognition.Four.residual_inverter_moves_of_full_orthogonal
    F.terminalRepresentation hr r hr2 hrinv (hatSpace F F.W) hw
  have hn : ⁅F.W,conjugate F.ZU g⁆ ≠ ⊥ := by
    intro hb
    have hcent : conjugate F.ZU g ≤ centralizer (F.W : Set G) := by
      rw [commutator_comm] at hb
      exact commutator_eq_bot_iff_le_centralizer.mp hb
    obtain ⟨a,ha,rfl⟩ := hrZ
    obtain ⟨u,hu,heu⟩ := (show w.toMul ∈ hatImage F F.W from hwW)
    apply hwmove
    apply Additive.toMul.injective
    rw [F.terminalRepresentation_apply_mk,←heu,F.terminalHatAction_apply_mk]
    apply congrArg (QuotientGroup.mk' (center F.U))
    apply Subtype.ext
    change (a : G) * (u : G) * (a : G)⁻¹ = (u : G)
    have he : (u : G) * (a : G) = (a : G) * (u : G) := mem_centralizer_iff.mp (hcent ha) u hu
    rw [←he,mul_assoc,mul_inv_cancel,mul_one]
  have hc : Nat.card (conjugate (F.Vi 1) g)=2 := by
    rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply eq_of_le_of_card_ge (rankTwo_center_commutator_le_conjugate_point h F d hne g hgP hgH)
  rw [hc]
  have hh := (one_lt_card_iff_ne_bot ⁅F.W,conjugate F.ZU g⁆).mpr hn
  omega

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
