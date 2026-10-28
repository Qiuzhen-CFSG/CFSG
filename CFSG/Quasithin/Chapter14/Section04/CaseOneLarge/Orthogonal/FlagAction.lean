module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

/-!
# Initial orthogonal reduction on the original flag

The natural Ω₄⁺(4) coordinates give binary dimension eight and hence
|U|=512. Its original Sylow containment gives |T|≥512. The same marked
action supplies the fixed line, conjugate-core product and centralizer
bounds from CoreGeometry, with every earlier geometric input discharged.

This is the original-flag entrance to 14.4.9. Constructing U=O₂(H), the
selected conjugate involution and its diagonal action remains necessary
before applying Orthogonal.Source; no such conclusion is assumed here.

Source: Aschbacher--Smith, 14.4.2(3), 14.4.6--9, printed pp.1006--1010.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal orthogonal action supplies the original order, fixed line,
conjugate core product and centralizer bounds used before selecting i=z^x.
The two-core equality and the selection are not assumed or asserted here. -/
theorem source_orthogonal_flag_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    let D := conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)
    Nat.card F.U = 512 ∧ 512 ≤ Nat.card T ∧
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
      conjugate (F.H.pCoreIn 2) g = conjugate F.U g ⊔ D ∧
      D ≤ F.H.pCoreIn 2 ∧ ⁅D,F.U⁆ ≤ F.Vi 1 ∧ ⁅D,F.W⁆ = ⊥ := by
  let := chosen.elementary
  let := F.U_normal
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have models : RankCore.ActionAlternative.{u} (sourceAction F hk) := .orthogonal κ e he
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 :=
    (e.trans Binary.binaryCoordinates).finrank_eq.trans Binary.finrank_binary
  have hz := (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
  have hc : Nat.card F.U = 512 := by
    have hqcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod,hd] at hqcard
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hz]
    change Nat.card (Additive F.Uhat) * 2 = 512
    norm_num only [hqcard]
  have hT : 512 ≤ Nat.card T := by
    rw [← hc]
    exact Nat.card_le_card_of_injective _
      (inclusion_injective (source_closure_le_sylow d earlier hq chosen structural alternatives F))
  exact ⟨hc,hT,source_fixed_space_of_marked_action d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH models,
    source_conjugate_core_product d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH,
    source_centralizer_bounds d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH models⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
