module
public import Theory.Representation.OrthogonalFourPlusMatrix.FixedLineGeneration
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Frame
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration.Transport
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
/-!
# Orthogonal residual generation and the relative centralizer

The original marked action has exactly the original flag line as its fixed
space. The determinant-module calculation forces both actual SL₂(4) factors
into the commutator with the conjugate actor, giving generation of the
literal two-residual image. Apply this at the inverse source transporter,
transport through Hᵍ/O₂(Hᵍ), and lift by two-perfectness to Kᵍ=[Kᵍ,W].

The previously proved centralizer bounds and the Three Subgroups Lemma give
Kᵍ ≤ C_G(D), where D=C_{Hᵍ}(Uᵍ). Sylow supplementation and the original
escape show Kᵍ is not contained in N_G(L). The genuine uniqueness theorem
therefore gives C_D(L)=1. Every quotient and conjugator is the original one;
no component-swap, residual-generation or uniqueness callback is assumed.

This completes the first paragraph of 14.4.7 for the marked orthogonal row.
The natural complement, U=O₂(H), the selected involution and the exhaustive
marked catalogue remain to be constructed from the original flag.

Source: Aschbacher--Smith, 14.4.2(3), 14.4.6--7,
printed pp.1006--1009, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Residual generation in the original orthogonal quotient. The original
fixed line rules out centralization of either determinant factor. -/
theorem source_orthogonal_quotient_generation (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
    ⁅K,((F.X g).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))⁆ = K := by
  let := chosen.elementary
  let := F.U_normal
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let X := ((F.X g).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let a := sourceAction F hk
  have models : RankCore.ActionAlternative.{u} a := .orthogonal κ e he
  have hf := source_fixed_space_of_marked_action d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH models
  obtain ⟨_,hx,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  have hqX : X.map q.toMonoidHom = F.terminalDot (F.X g) := by
    rw [map_map]
    rfl
  have hfix : fixedSpace a.representation X = Submodule.span (ZMod 2) {v} := by
    change fixedSpace (F.terminalRepresentation.comp q.toMonoidHom) X = _
    rw [fixedSpace_comp_map,hqX,hf,hline]
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  let E : Additive F.Uhat ≃ₗ[ZMod 2] Binary.V := e.trans Binary.binaryCoordinates
  have hm (k : K) (w : Additive F.Uhat) : E (a.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (a.representation k w)) = _
    rw [he]
    obtain ⟨b,hb⟩ := elementaryEquiv.surjective (κ k)
    have hb' : κm k = b := by
      change elementaryEquiv.symm (κ k) = b
      rw [← hb,elementaryEquiv.symm_apply_apply]
    rw [← hb,hb']
    exact toOrthogonal_coordinates b (e w)
  exact Binary.commutator_eq_of_fixed_line a.representation K X κm E hm v hyp.point_ne_zero hfix

/-- Symmetry at the inverse of the source conjugator gives generation of
the literal embedded two-residual of Hᵍ by the original W. -/
theorem source_orthogonal_residual_generation (d : Counterexample T L)
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
    conjugate ((pResidual 2 F.H).map F.H.subtype) g =
      ⁅conjugate ((pResidual 2 F.H).map F.H.subtype) g,F.W⁆ := by
  let := chosen.elementary
  let := F.U_normal
  let a := earlierGeometry d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hgen := source_orthogonal_quotient_generation d earlier hq chosen structural alternatives
    F hne hZ g⁻¹ ((F.P L).inv_mem hgP) (fun h => hgH (inv_mem_iff.mp h)) κ e he
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)] at hgen
  have hs := RankCore.CentralizerGeometry.ModelGeneration.star_generation_transport F.H F.W g hgen
  have hW : F.W ≤ conjugate F.H g := by
    change RankCore.CentralizerGeometry.W F.U (F.Vi 2) ≤
      RankCore.CentralizerGeometry.conjugate F.H g
    rw [a.H_eq_centralizer,RankCore.CentralizerGeometry.conjugate_centralizer]
    exact inf_le_right.trans (centralizer_le a.conjugate_line_le_plane)
  change RankCore.CentralizerGeometry.conjugate ((pResidual 2 F.H).map F.H.subtype) g =
    ⁅RankCore.CentralizerGeometry.conjugate ((pResidual 2 F.H).map F.H.subtype) g,F.W⁆
  rw [RankCore.CentralizerGeometry.conjugate_residual]
  exact RankCore.CentralizerGeometry.ambient_residual_generation _ _ hW hs

/-- The source uniqueness theorem kills the literal C_D(L), completing the
first paragraph of 14.4.7 for the original orthogonal flag. -/
theorem source_orthogonal_centralizer_trivial (d : Counterexample T L)
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
    conjugate ((pResidual 2 F.H).map F.H.subtype) g ≤ centralizer (D : Set G) ∧
      D ⊓ centralizer (L : Set G) = ⊥ := by
  let := chosen.elementary
  let := F.U_normal
  let a := earlierGeometry d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  let D := conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)
  let K := (pResidual 2 F.H).map F.H.subtype
  let M := normalizer (L : Set G)
  let h := higherRankHypothesis d earlier hq chosen
  have hgen := source_orthogonal_residual_generation d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  have models : RankCore.ActionAlternative.{u} (sourceAction F
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)) := .orthogonal κ e he
  have hDW := (source_centralizer_bounds d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH models).2.2
  have hHD : conjugate F.H g ≤ normalizer (D : Set G) :=
    RankCore.CentralizerGeometry.relative_centralizer_normalized _ _
      (RankCore.CentralizerGeometry.conjugate_normalizes F.H F.U g a.normalizes)
  have hKD : conjugate K g ≤ centralizer (D : Set G) := by
    rw [hgen]
    exact RankCore.CentralizerGeometry.commutator_centralizes_of_normalizes _ _ _
      ((map_mono (map_subtype_le _)).trans hHD) hDW
  have hjoin : L ⊔ conjugate (T : Subgroup G) g = L ⊔ (T : Subgroup G) := by
    have hh := RankCore.CentralizerGeometry.conjugate_eq_self (L ⊔ (T : Subgroup G))
      ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hg))
    rw [RankCore.CentralizerGeometry.conjugate,Subgroup.map_sup] at hh
    change RankCore.CentralizerGeometry.conjugate L g ⊔
      RankCore.CentralizerGeometry.conjugate (T : Subgroup G) g = _ at hh
    rwa [RankCore.CentralizerGeometry.conjugate_eq_self L (L.le_normalizer hg)] at hh
  have hTL : conjugate (T : Subgroup G) g ≤ normalizer (L : Set G) := by
    have hh := RankCore.CentralizerGeometry.conjugate_normalizes (T : Subgroup G) L g
      (h.sylow_normalizes structural)
    rwa [RankCore.CentralizerGeometry.conjugate_eq_self L (L.le_normalizer hg)] at hh
  have hKM : ¬ conjugate K g ≤ M := by
    intro hh
    have hK : K ≤ M := by
      have hi : RankCore.CentralizerGeometry.conjugate
          (RankCore.CentralizerGeometry.conjugate K g) g⁻¹ ≤
          RankCore.CentralizerGeometry.conjugate M g⁻¹ := map_mono hh
      rwa [RankCore.CentralizerGeometry.conjugate_conjugate,mul_inv_cancel,
        RankCore.CentralizerGeometry.conjugate_one,
        RankCore.CentralizerGeometry.conjugate_eq_self M
          (M.le_normalizer (M.inv_mem (L.le_normalizer hg)))] at hi
    have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
    have hs : K ⊔ (T : Subgroup G) = F.H := by
      have hh := congrArg (Subgroup.map F.H.subtype)
        (pResidual_sup_sylow_eq_top (T.subtype hTH))
      rwa [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
        ← MonoidHom.range_eq_map,range_subtype] at hh
    exact h.flag_escape F alternatives (hs ▸ sup_le hK (h.sylow_normalizes structural))
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ conjugate (T : Subgroup G) g ≤ N → N = M := by
    have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
      intro X _ _ hX S A hA
      exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
    intro N hN hLN
    rw [hjoin] at hLN
    exact Set.mem_singleton_iff.mp ((h.maximal_unique structural unique).2 ▸
      show N ∈ {P : Subgroup G | IsMaximalTwoLocal P ∧ L ⊔ (T : Subgroup G) ≤ P}
        from ⟨hN,hLN⟩)
  exact ⟨hKD, RankCore.CentralizerGeometry.relative_centralizer_eq_bot_of_unique
    (conjugate K g) D L (conjugate (T : Subgroup G) g) M a.D_isTwoGroup hKD
    ((map_mono (F.invariant 1)).trans hHD) hTL hu hKM⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
