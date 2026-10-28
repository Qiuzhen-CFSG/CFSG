module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Preparation
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.KernelReduction

/-!
# The original extraspecial inputs to 14.4.8

The natural action identifies the plane parabolic and its two-residual.
The binary parabolic calculation then identifies I₂ with both ⟨U,Uᵍ⟩
and L₂U, and gives the full order-six action on the original plane.
The two distinct central lines force the fixed-space clause: a subgroup
of E whose commutators with Wᵍ lie in both lines centralizes Wᵍ, and hence
lies in its center V₂. Every subgroup here is the literal subgroup of the
original invariant flag.

This discharges EarlierExtraspecialData from the original counterexample,
chosen module and center-point equality. Only the authorized earlier
naturality, structural and escape implications remain explicit. The
application to the full local action is in CaseOneLarge.LocalAction.

Source: Aschbacher--Smith, 12.8.8--11, printed pp.851--854;
14.4.8, printed p.1009.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem normal_residual_sup_sylow (N : Subgroup G) [N.Normal] (T : Sylow 2 G) :
    twoResidual N ⊔ (T : Subgroup G) = N ⊔ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal N
  have hh := congrArg (map N.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, hS, subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, range_subtype] at hh
  apply le_antisymm (sup_le_sup (map_subtype_le _) le_rfl)
  apply sup_le _ le_sup_right
  exact hh.ge.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))

private theorem residual_sup_sylow (N : Subgroup G) (T : Sylow 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (N : Set G)) :
    twoResidual N ⊔ (T : Subgroup G) = N ⊔ (T : Subgroup G) := by
  let K := N ⊔ (T : Subgroup G)
  let D := N.subgroupOf K
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le N.le_normalizer hn)
  have hNK : N ≤ K := le_sup_left
  have hTK : (T : Subgroup G) ≤ K := le_sup_right
  have hh := congrArg (map K.subtype) (normal_residual_sup_sylow D (T.subtype hTK))
  have hDN : D.map K.subtype = N := map_subgroupOf_eq_of_le hNK
  have hR : (twoResidual D).map K.subtype = twoResidual N := by
    change ((pResidual 2 D).map D.subtype).map K.subtype = _
    rw [map_embedded_pResidual, hDN]
    rfl
  simpa only [Subgroup.map_sup, hR, Sylow.coe_subtype, hDN,
    map_subgroupOf_eq_of_le hTK] using hh

/-- The whole plane parabolic is L₂T, for the original natural action. -/
theorem plane_parabolic_eq (a : NaturalThreeAction L V T)
    (F : InvariantFlag T V 3) : F.P L = F.Li L 2 ⊔ (T : Subgroup G) := by
  have hP : F.P L = (L ⊔ (T : Subgroup G)) ⊓ F.Gi 2 := by
    unfold P
    congr 1
    apply le_antisymm
    · exact iInf_le_of_le 2 (iInf_le_of_le (by omega) le_rfl)
    · apply le_iInf; intro i; apply le_iInf; intro hi
      have : i = 2 := by omega
      subst i
      exact le_rfl
  have hn : (T : Subgroup G) ≤ normalizer (L ⊓ F.Gi 2 : Set G) :=
    (le_inf a.T_normalizes ((F.invariant 2).trans (F.Gi 2).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [hP, NaturalFlags.Li_eq_residual, residual_sup_sylow _ T hn]
  apply le_antisymm
  · rintro x ⟨hx, hxH⟩
    obtain ⟨b, hb, t, ht, rfl⟩ :=
      (coe_mul_of_right_le_normalizer_left L (T : Subgroup G) a.T_normalizes ▸ hx)
    have hbH : b ∈ F.Gi 2 := by
      simpa only [mul_inv_cancel_right] using
        (F.Gi 2).mul_mem hxH ((F.Gi 2).inv_mem (F.invariant 2 ht))
    exact mul_mem_sup ⟨hb, hbH⟩ ht
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right (F.invariant 2))

/-- Its embedded two-residual is the original L₂. -/
theorem plane_parabolic_residual (a : NaturalThreeAction L V T)
    (F : InvariantFlag T V 3) :
    (pResidual 2 (F.P L)).map (F.P L).subtype = F.Li L 2 := by
  rw [plane_parabolic_eq a F]
  apply embedded_pResidual_join_pGroup _ _ _ T.isPGroup' (NaturalFlags.Li_normalized a F 2)
  rw [NaturalFlags.Li_eq_residual]
  exact isPPerfect_embedded_pResidual 2 _

/-- Both commutators and squares of the actual closure lie in the marked point. -/
theorem source_commutator_squares (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    ⁅F.U, F.U⁆ ≤ F.Vi 1 ∧ ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  exact F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F alternatives)

/-- Construct all earlier extraspecial inputs to 14.4.8 on the original flag.
The generated-subgroup identity is retained for the literal I₂ consumer. -/
theorem source_extraspecial_data (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    EarlierExtraspecialData T (F.Vi 2) (F.E g) F.U (conjugate F.U g)
      (F.Vi 1) (conjugate (F.Vi 1) g) (F.X g) (F.Li L 2) ∧
      F.I₂ L = F.U ⊔ conjugate F.U g := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  have a := source_natural_action d earlier hq chosen structural
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨e, hres, hgen, _, hIG, hIN, _, _, _, _, _, _, heval⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  have hcore := (F.binary_source_core_and_intersection (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
    hcomm hsquare hspan hne g hgP hgH).1
  let := hIN
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hXU : F.X g ≤ conjugate F.U g := map_mono inf_le_left
  have hnorm : F.U ⊔ conjugate F.U g ≤ normalizer (F.Vi 2 : Set G) := by
    rw [← hgen]
    exact hIG
  have hplane := F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  refine ⟨{
    V₂_le_T := (F.le_seed 2).trans chosen.le_sylow
    T_normalizes_V₂ := F.invariant 2
    U_le_T := source_closure_le_sylow d earlier hq chosen structural alternatives F
    Wg_le_T := F.X_le_T_of_core L g hIG hcore
    Wg_le_Ug := hXU
    E_le := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hXU)
    U_commutator := hcomm
    Ug_commutator := ?_
    U_center := ?_
    Z_card := hcard
    Zg_card := ?_
    V₂_card := by simpa using F.card 2 (by decide)
    plane := hplane
    fixed := ?_
    supplement := ?_
    plane_normalizes := hnorm
    plane_image_card := ?_
    plane_centralizer := F.X_le_plane_centralizer g hgG }, hgen⟩
  · exact (le_of_eq (map_commutator F.U F.U (MulAut.conj g⁻¹).toMonoidHom).symm).trans
      (map_mono hcomm)
  · rw [← centerIn_eq_inf_centralizer]
    exact hZ
  · rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  · obtain ⟨htwo, hphi, hc⟩ := source_closure d earlier hq chosen structural alternatives F hne
    let := F.uhat_elementary_of_point (by decide) htwo hphi
    let B := F.localKernel_markedForm (by decide) htwo hphi hcomm
    have hZX : Chapter12.Section08.centerIn (F.X g) = F.Vi 2 := by
      rw [F.conjugate_centralizer_center (by decide) L chosen.normalizes hc
        (F.plane_centralizer_center B) g hgP hgH, hZ, sup_comm]
      exact hplane.symm
    have hdisj : conjugate (F.Vi 1) g ⊓ F.Vi 1 = ⊥ := by
      simpa only [hZ] using
        F.conjugate_point_inf_ZU (by decide) hc g (chosen.normalizes hg) hgH
    intro D hD hDZ
    have hDZg : ⁅D, F.X g⁆ ≤ conjugate (F.Vi 1) g := by
      calc
        ⁅D, F.X g⁆ ≤ ⁅conjugate F.U g, conjugate F.U g⁆ :=
          commutator_mono (hD.trans (inf_le_right.trans hXU)) hXU
        _ = conjugate ⁅F.U, F.U⁆ g := (map_commutator _ _ _).symm
        _ ≤ conjugate (F.Vi 1) g := map_mono hcomm
    have hbot : ⁅D, F.X g⁆ = ⊥ := le_bot_iff.mp ((le_inf hDZg hDZ).trans hdisj.le)
    rw [← hZX, centerIn_eq_inf_centralizer]
    exact le_inf (hD.trans inf_le_right) (commutator_eq_bot_iff_le_centralizer.mp hbot)
  · rw [← hgen, hres, plane_parabolic_residual a F]
  · have hIGnorm : F.I₂ L ≤ normalizer (F.Vi 2 : Set G) := hIG
    have hsurj : Function.Surjective (conjugation (F.I₂ L) (F.Vi 2) hIGnorm) := by
      intro b
      obtain ⟨q, hq⟩ := e.surjective (F.binaryPlaneLabel (by decide) b)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L)) q
      change e (x : (F.I₂ L) ⧸ pCore 2 (F.I₂ L)) = _ at hq
      refine ⟨x, ?_⟩
      ext v
      rw [conjugation_apply, ← heval x v, hq, MulEquiv.symm_apply_apply]
    have hrange : (conjugation (F.U ⊔ conjugate F.U g) (F.Vi 2) hnorm).range = ⊤ := by
      apply MonoidHom.range_eq_top.mpr
      have transport (J : Subgroup G) (hJ : J ≤ normalizer (F.Vi 2 : Set G))
          (he : F.I₂ L = J) : Function.Surjective (conjugation J (F.Vi 2) hJ) := by
        subst J
        exact hsurj
      exact transport _ _ hgen
    rw [hrange, Nat.card_congr (Subgroup.topEquiv).toEquiv,
      Nat.card_congr (F.binaryPlaneLabel (by decide)).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
