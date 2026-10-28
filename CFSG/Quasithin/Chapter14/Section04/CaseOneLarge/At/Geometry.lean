module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNondegenerateExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.ActionAlternatives
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Preparation
import all CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExtraspecialInputs
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Terminal
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedPoint
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLine
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Solvable
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Nonsolvable
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueReduction
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

/-!
# The original large closure and terminal action at G,T

The natural marking gives the literal extraspecial closure and its central quotient.
The point and conjugate-actor calculations retain both G.11 fixed-point clauses,
the exact kernel and Sylow placement. The square form excludes the solvable
large action, and the actual core geometry gives the remaining rank bounds.

The earlier inputs are restricted to the original group and Sylow subgroup.
The universal APIs remain unchanged. The `import all` edges intentionally
reuse the private calculations of the corresponding source implementation;
only deductions depending on the earlier inputs are specialized here.
Source: Aschbacher--Smith, 12.8.8--13, 14.4.1--2,7; printed pp.852--856,1006--1009; refs/quasithin.pdf.
-/

public noncomputable section

/- Specialization of CaseOneLarge/Geometry.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_extraspecial_order_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) :
    IsExtraspecial 2 F.U ∧ (Nat.card F.U = 32 ∨ 64 < Nat.card F.U) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hc⟩ := CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have hcenter : Nat.card (center F.U) = 2 := by
    rw [center_point F hZ]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show F.Vi 1 ≤ F.U from (F.le_seed 1).trans (le_conjugateSpanBy V F.H))).toEquiv).trans
      (by simpa using F.card 1 (by decide))
  refine ⟨⟨hcenter, inferInstance,
    QuotientGroup.nontrivial_iff.mpr (fun ht => hne (center_eq_top_iff.mp ht))⟩, ?_⟩
  obtain ⟨hd, heven⟩ := quotient_dimension F htwo hphi hc
  let r := Module.finrank (ZMod 2) (Additive F.Uhat)
  have hcard : Nat.card F.U = 2 ^ (r + 1) := by
    have hqcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod] at hqcard
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
    change Nat.card (Additive F.Uhat) * 2 = _
    rw [hqcard, pow_succ]
  by_cases hr : r = 4
  · exact Or.inl (by rw [hcard, hr]; decide)
  · right
    obtain ⟨k, hk⟩ := heven
    have hlarge : 6 < r + 1 := by dsimp [r]; omega
    rw [hcard]
    exact (by decide : 64 = 2 ^ 6) ▸ Nat.pow_lt_pow_right (by decide) hlarge

theorem source_large_overgroup_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : Nat.card F.U ≠ 32)
    (G₀ : Subgroup G) (hTG₀ : (T : Subgroup G) ≤ G₀)
    (e : G₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) : False := by
  have hcard := (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).2
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hbound := Matrix.PSL4Two.card_twoGroup_le_sixtyFour T.isPGroup'
    (e.toMonoidHom.comp (inclusion hTG₀)) (e.injective.comp (inclusion_injective hTG₀))
  have hle := Nat.card_le_card_of_injective (inclusion hUT) (inclusion_injective hUT)
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry

end

/- Specialization of CaseOneLarge/ExtraspecialInputs.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_extraspecial_data_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    EarlierExtraspecialData T (F.Vi 2) (F.E g) F.U (conjugate F.U g)
      (F.Vi 1) (conjugate (F.Vi 1) g) (F.X g) (F.Li L 2) ∧
      F.I₂ L = F.U ⊔ conjugate F.U g := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have a := source_natural_action_at d earlier hq chosen structural
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨e, hres, hgen, _, hIG, hIN, _, _, _, _, _, _, heval⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hcore := (F.binary_source_core_and_intersection (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
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
    U_le_T := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
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
  · obtain ⟨htwo, hphi, hc⟩ := CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne
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

end

/- Specialization of CaseOneLarge/Terminal.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped Pointwise IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable (F : InvariantFlag T V 3) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]

omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
theorem source_terminal_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) :
    F.terminalHatAction.ker = pCore 2 F.H := by
  let := chosen.elementary
  exact terminal_kernel_of_center_point F
    (source_closure_geometry_at F d earlier hq chosen structural alternatives hne) hZ

omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
theorem source_terminal_conjugate_center_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) = ⊥ := by
  let := chosen.elementary
  have hplane := F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH
  have hZU : conjugate F.ZU g ≤ F.U := by
    rw [hZ]
    exact le_sup_right.trans (hplane.ge.trans ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)))
  have htwo := (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).1
  have hUcore : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes htwo F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)
  change ((conjugate F.ZU g).subgroupOf F.H).map
    (QuotientGroup.mk' F.terminalHatAction.ker) = ⊥
  apply le_bot_iff.mp
  rw [map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk',
    source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ]
  intro x hx
  have hm := hUcore (hZU hx)
  obtain ⟨y, hy, he⟩ := hm
  exact (show y = x from Subtype.ext he) ▸ hy

omit [IsElementaryAbelian 2 V] in
theorem source_terminal_rank_balance_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    finrank (ZMod 2) (hatSpace F (F.E g)) + Group.rank (F.terminalDot (F.X g)) =
      finrank (ZMod 2) (Additive F.Uhat) - 1 := by
  obtain ⟨_, heX, B, v, hyp⟩ :=
    source_terminal_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hd := hyp.dimension
  have hbot : ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) = ⊥ := by
    rw [source_terminal_conjugate_center_at F d earlier hq chosen structural alternatives hne hZ g hgP hgH]
    simp only [bot_subgroupOf]
  rw [hbot, Group.rank_congr (QuotientGroup.quotientBot)] at hd
  exact hd

omit [IsElementaryAbelian 2 V] in
theorem source_large_terminal_irreducible_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U) : IsIrreducible F.terminalRepresentation := by
  obtain ⟨g, _, hgP, hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_, heX, B, v, hyp⟩ :=
    source_terminal_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  by_contra hred
  have hd := (hyp.reducible_degree_and_solvable hred).1
  have hcenter := (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
  have hquot := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
  rw [Nat.card_zmod, hd] at hquot
  have hcard : Nat.card F.U = 32 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
    change Nat.card (Additive F.Uhat) * 2 = 32
    norm_num only [hquot]
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedPoint.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_parabolic_displacement_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x,u⁆ * e = w := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨ι, ⟨M⟩⟩ := F.binary_source_parabolic_natural_module (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
    hcomm hsquare hspan hne g hgP hgH
  obtain ⟨_, _, hgen, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
    hcomm hsquare hspan hne g hgP hgH
  have hnE := F.binary_source_E_normalized L chosen.normalizes g hgP hgen.symm hcomm
  let : ((F.E g).subgroupOf F.W).Normal := normal_subgroupOf_of_le_normalizer
    ((show F.W ≤ F.I₂ L from inf_le_left.trans (le_conjugateSpanBy _ _)).trans hnE)
  intro u hu huw w hw
  let uU : F.U := ⟨u, hu⟩
  have hcm : ∀ x ∈ F.X g, ⁅x,u⁆ ∈ F.W := fun x hx =>
    M.commutator_mem_W uU huw x ((le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx)
  obtain ⟨x, hx⟩ := F.parabolicCommutator_natural_surjective L g M uU huw hcm
    M.commutator_core_le (QuotientGroup.mk' ((F.E g).subgroupOf F.W) ⟨w, hw⟩)
  have he : ⁅(x:G),u⁆⁻¹ * w ∈ F.E g := by
    change (⟨⁅(x:G),u⁆, hcm x x.property⟩ : F.W)⁻¹ * ⟨w,hw⟩ ∈ (F.E g).subgroupOf F.W
    rw [← QuotientGroup.ker_mk' ((F.E g).subgroupOf F.W)]
    exact (MonoidHom.eq_iff (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).mp hx.symm
  exact ⟨x, x.property, _, he, mul_inv_cancel_left _ _⟩

theorem source_fixed_point_alternative_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2) ∨
      ∃ x ∈ F.terminalDot (F.X g), x ≠ 1 ∧
        finrank (ZMod 2) (Symplectic.movedSpace F F.terminalHatAction x) ≤ 2 ∧
        hatSpace F (F.Vi 2) ≤ Symplectic.movedSpace F F.terminalHatAction x := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  have hg : g ∈ F.Gi 2 := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  obtain ⟨e, _, hgen, _, hIG, _, _, _, _, _, _, hindex, heval⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  let B := F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  have hB := marked_form_zero F hcomm B
  have hc := F.binary_source_center_calculations (by decide) L chosen.normalizes
    ((pResidual_eq_top_iff 2 L).mp h.residual) (h.sylow_normalizes_at structural)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT_at structural) c.seed_center
    hcomm hsquare hspan hne g hgP hgH c.tilde_kernel B
  have hdis := disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L
    chosen.normalizes c.seed_center g hgP hgH).1
  have hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g := by
    simpa only [inf_comm] using hc.2.2.2.2.2.2.2.2.1
  have hfour : hatSpace F (F.E g) ⊓ XfixedSpace F F.terminalHatAction g =
      hatSpace F (F.Vi 2) :=
    EhatFixed_eq_plane F g hg hcomm hdis hc.1 hZg B.form hB B.nondegenerate B.alternating.isRefl
  by_cases heq : XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2)
  · exact Or.inl heq
  right
  have hstrict : hatSpace F (F.Vi 2) < XfixedSpace F F.terminalHatAction g :=
    lt_of_le_of_ne (hfour ▸ inf_le_right) (Ne.symm heq)
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [c.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  have hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hIG)) := by
    intro a
    obtain ⟨i, hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L))
      (e.symm (F.binaryPlaneLabel (by decide) a))
    refine ⟨i, ?_⟩
    ext v
    change (i:G)*(v:G)*(i:G)⁻¹ = (a v:G)
    rw [← heval i v]
    change ((F.binaryPlaneLabel (by decide)).symm (e (QuotientGroup.mk' _ i)) v : G) = _
    rw [hi, e.apply_symm_apply, MulEquiv.symm_apply_apply]
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hi : ∀ (a : F.H) (u v : F.Uhat),
      B.form (Additive.ofMul (F.terminalHatAction a u)) (Additive.ofMul (F.terminalHatAction a v)) =
        B.form (Additive.ofMul u) (Additive.ofMul v) := by
    intro a u v
    change F.uhatBilinearForm (by decide) c.two c.frattini_point
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a v)) = _
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) c.two c.frattini_point]
    rfl
  exact exists_lowRank_of_fixedSpace_lt F (by decide) hne c.two hPhi c.seed_center L g hg
    hdis z hzp hz hIG hfull F.terminalHatAction F.terminalHatAction_apply_mk
    (F.binary_source_action_kernel_intersections (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hcomm hsquare hspan hne
      c.seed_center g hgP hgH).1 hindex
    (source_parabolic_displacement_at d earlier hq chosen structural alternatives F hne g hgP hgH)
    hc.1 B.form B.nondegenerate B.alternating hB hi hfour hstrict

theorem source_terminal_fixed_point_alternative_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} ∨
      ∃ a : F.terminalDot (F.X g), a ≠ 1 ∧
        finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - LinearMap.id)) ≤ 2 ∧
        v ∈ LinearMap.range (F.terminalRepresentation a - LinearMap.id) := by
  rcases source_fixed_point_alternative_at d earlier hq chosen structural alternatives F hne
      g hgP hgH with hf | ⟨a, ha, hane, hr, hm⟩
  · exact Or.inl ((terminal_fixed_space_eq F g).trans (hf.trans hline.symm))
  · exact Or.inr ⟨⟨a, ha⟩, fun he => hane (congrArg Subtype.val he), hr,
      hm (hline ▸ Submodule.mem_span_singleton_self v)⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLine.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_terminal_ranks_of_no_lowRank_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat)
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v
      (F.terminalDot (F.X g))) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
      2 * finrank (ZMod 2) (hatSpace F (F.E g)) = finrank (ZMod 2) (Additive F.Uhat) ∧
      Group.rank (F.terminalDot (F.X g)) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) ∧
      ∀ a b : F.terminalDot (F.X g),
        (∀ w : hatSpace F (F.E g), F.terminalRepresentation a w = F.terminalRepresentation b w) →
        a = b := by
  have hf : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} := by
    rcases source_terminal_fixed_point_alternative_at d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
    · exact hf
    · exact (hn ⟨a,a.property,hr,hv⟩).elim
  obtain ⟨_,heX,B,v',hyp,hline',_⟩ :=
    source_terminal_marked_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hv' : v' ∈ Submodule.span (ZMod 2) {v} :=
    hline.symm ▸ (hline' ▸ Submodule.mem_span_singleton_self v')
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv'
  have hc1 : c = 1 := by
    have hb := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hb with he | he
    · exact (hyp.point_ne_zero (by simpa [he] using hc.symm)).elim
    · exact he
  have hv : v = v' := by simpa only [hc1,one_smul] using hc
  rw [← hv] at hyp
  have hzero : ((F.terminalDot (conjugate F.ZU g)).subgroupOf
      (F.terminalDot (F.X g))) = ⊥ := by
    rw [source_terminal_conjugate_center_at F d earlier hq chosen structural alternatives hne hZ g hgP hgH]
    exact bot_subgroupOf _
  obtain ⟨he,_,hinj⟩ := FixedLine.ranks_of_no_lowRank hyp hf hzero hn
  have hr := source_terminal_rank_balance_at F d earlier hq chosen structural alternatives hne hZ g hgP hgH
  have hvpos : 0 < finrank (ZMod 2) (Additive F.Uhat) := by
    let : Nontrivial (Additive F.Uhat) := ⟨⟨v,0,hyp.point_ne_zero⟩⟩
    exact Module.finrank_pos
  exact ⟨hf.trans hline,he,by omega,hinj⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Solvable.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

universe u v

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_terminal_not_solvable_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U) :
    ¬ Group.IsSolvable F.TerminalHdot := by
  let := chosen.elementary
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let := F.uhat_elementary_of_point (by decide) c.two c.frattini_point
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_, heX, B, v, hyp⟩ :=
    source_terminal_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hirr := source_large_terminal_irreducible_at F d earlier hq chosen structural alternatives hne hZ hlarge
  let q := F.uhatQuadraticForm (by decide) c.two c.frattini_point
    (center_frattini_bot_of_center_point F c hZ)
  obtain ⟨hqs, hqi, hqn⟩ := quadratic_intersection_of_center_point F c (by decide) hZ g
    (disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
      c.seed_center g hgP hgH).1)
  have hterminal (a : F.TerminalHdot) (w : Additive F.Uhat) :
      q (F.terminalRepresentation a w) = q w := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hqi a w.toMul
  have hdim : 4 < finrank (ZMod 2) (Additive F.Uhat) := by
    have hcenter := (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
    have hcard : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
      change Nat.card (Additive F.Uhat) * 2 = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, pow_succ]
    by_contra hh
    have hb := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 5)
    rw [← hcard] at hb
    norm_num at hb
    omega
  intro hs
  exact false_of_solvable_large_quadratic hyp (source_terminal_cover F d chosen)
    hs hirr hdim q hqn hqs hterminal

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Nonsolvable.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_terminal_actor_normal_in_sylow_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    F.terminalDot (F.X g) ≤ (P : Subgroup F.TerminalHdot) ∧
      ((F.terminalDot (F.X g)).subgroupOf (P : Subgroup F.TerminalHdot)).Normal := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨e, _, hgen, _, hIG, hIN, _, _, hfactor, hPH, hcore, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hcore' := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  exact Xdot_normal_in_Tdot F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) L g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hcore'
    F.terminalHatAction F.terminalHatAction_apply_mk

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/CatalogueReduction.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_lowRank_reduction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
      (IsIrreducible F.terminalRepresentation ∧
        6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ChapterG.Section11.ExchangedRecognition.RemainingComponentModels F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v
      (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow_at d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  rcases ChapterG.Section11.ExchangedRecognition.corrected_conclusion_or_remaining hyp
    (source_terminal_cover F d chosen) hw hS with (hc | hex) | ⟨hi,hd,hs | hn⟩
  · exact Or.inl hc
  · exact (CaseOneHS.source_no_full_linear_alternative_at d earlier hq chosen structural alternatives
      F hne B v _ _ _ hex).elim
  · exact (source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
      F hne hZ hlarge hs.1).elim
  · exact Or.inr ⟨hi,hd,hn.2⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/CoreGeometry.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative



open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_symmetric_quotient_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    RankCore.CentralizerGeometry.QuotientKernel F.U (conjugate F.U g) (F.Vi 2) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  have hc := (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  have hgiP := (F.P L).inv_mem hgP
  have hgiH : g⁻¹ ∉ F.H := fun hg => hgH (inv_mem_iff.mp hg)
  have hgi := F.P_le_G₂ (by decide) L chosen.normalizes hgiP
  have hk := (F.binary_source_parabolic_action_clauses (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
    hcomm hsquare hspan hne hc g⁻¹ hgiP hgiH).2.1.1
  have hX : RankCore.CentralizerGeometry.W (conjugate F.U g) (F.Vi 2) = F.X g := by
    have hgn := F.P_le_G₂ (by decide) L chosen.normalizes hgP
    change conjugate F.U g ⊓ centralizer (F.Vi 2 : Set G) = conjugate F.W g
    rw [W, conjugate_inf]
    congr 1
    apply Eq.symm
    exact (conjugate_eq_iff _ g).mpr ((normalizer_le_normalizer_centralizer _) hgn)
  have hz : RankCore.CentralizerGeometry.Z (conjugate F.U g) = conjugate F.ZU g :=
    centerIn_conjugate F.U g
  intro w hw
  rw [hz,hX]
  change (∀ u ∈ conjugate F.U g, ⁅w,u⁆ ∈ conjugate F.ZU g) ↔ w ∈ F.W ⊓ F.X g
  have hw' : MulAut.conj g w ∈ F.X g⁻¹ := by
    change MulAut.conj g w ∈ F.W.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
    rw [inv_inv]
    exact mem_map_of_mem _ hw
  have criterion : (∀ u ∈ conjugate F.U g, ⁅w,u⁆ ∈ conjugate F.ZU g) ↔
      MulAut.conj g w ∈ F.E g⁻¹ := by
    rw [← hk, F.mem_xHatKernel]
    constructor
    · intro hh
      refine ⟨hw', ?_⟩
      intro a ha
      have hm : MulAut.conj g⁻¹ a ∈ conjugate F.U g := mem_map_of_mem _ ha
      have he := (conjugate_mem_iff F.ZU g _).mp (hh _ hm)
      simpa [map_commutatorElement, MulAut.conj_apply, mul_assoc] using he
    · rintro ⟨_,hh⟩ u hu
      apply (conjugate_mem_iff F.ZU g _).mpr
      rw [map_commutatorElement]
      exact hh _ ((conjugate_mem_iff F.U g u).mp hu)
  rw [criterion]
  change (MulAut.conj g w ∈ F.W ∧ MulAut.conj g w ∈ F.X g⁻¹) ↔
    (w ∈ F.W ∧ w ∈ F.X g)
  constructor
  · rintro ⟨hh,_⟩
    exact ⟨hw,(conjugate_mem_iff F.W g w).mpr hh⟩
  · rintro ⟨_,hh⟩
    exact ⟨(conjugate_mem_iff F.W g w).mp hh,hw'⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension

universe u w

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

@[expose] def earlierGeometry_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.CentralizerGeometry.EarlierGeometry (V := Additive F.Uhat)
      F.H F.U (F.Vi 1) (F.Vi 2) L g := by
  let := chosen.elementary
  let := F.U_normal
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have hcomm := (source_commutator_squares_at d earlier hq chosen structural alternatives F).1
  let B := F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  refine {
    U_le_H := F.U_le_H
    H_eq_centralizer := ?_
    center_eq := hZ
    V₂_le_U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
    A_le_V₂ := F.monotone (by decide)
    g_normalizes := F.P_le_G₂ (by decide) L chosen.normalizes hgP
    g_mem_L := hg
    g_not_mem_H := hgH
    disjoint := ?_
    quotient_kernel := source_symmetric_quotient_kernel_at d earlier hq chosen
      structural alternatives F hne g hgP hgH
    action := sourceAction F hk
    hyperplane := ?_
    line := ?_ }
  · have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    exact le_antisymm (normalizer_le_centralizer_of_card_two _ hc) (Subgroup.centralizer_le_normalizer _)
  · have hh := F.conjugate_point_inf_ZU (by decide) c.seed_center g (chosen.normalizes hg) hgH
    simpa only [hZ, inf_comm, RankCore.CentralizerGeometry.conjugate,
      Chapter12.Section08.conjugate] using hh
  · rw [sourceAction_image]
    exact F.finrank_quotient_hat_centralizer (by decide) c.seed_center B
  · rw [sourceAction_image]
    exact finrank_hatSpace_plane F (by decide) c.seed_center

theorem source_centralizer_bounds_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ))) :
    let D := conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)
    D ≤ F.H.pCoreIn 2 ∧ ⁅D,F.U⁆ ≤ F.Vi 1 ∧ ⁅D,F.W⁆ = ⊥ := by
  let := chosen.elementary
  let := F.U_normal
  let e := earlierGeometry_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have heact : e.action = sourceAction F hk := rfl
  have hr : ∀ a : F.H ⧸ pCore 2 F.H, orderOf a = 2 →
      2 < e.action.movedRank a ∨ (e.action.movedRank a = 2 ∧
        ¬ e.action.image ((F.Vi 2).subgroupOf F.H) ≤ e.action.moved a) := by
    intro a ha
    rw [heact, sourceAction_image]
    exact sourceAction_rank_obstruction F hk
      (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2 models a ha
  exact e.centralizer_bounds hr

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension

universe u w

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_conjugate_core_product_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate (F.H.pCoreIn 2) g = conjugate F.U g ⊔
      (conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)) := by
  let := chosen.elementary
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point (by decide) c.two c.frattini_point
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1
  let := F.U_normal
  exact (earlierGeometry_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH).core_lift

theorem source_fixed_space_of_marked_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ))) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) := by
  let := chosen.elementary
  let := F.U_normal
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  obtain ⟨_,hx,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  rcases source_terminal_fixed_point_alternative_at d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,hane,hr,hm⟩
  · exact hf.trans hline
  · have ha2 : (a : F.TerminalHdot)^2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (F.terminalDot (F.X g))) a)
    have ha : orderOf (a : F.TerminalHdot) = 2 := orderOf_eq_prime_iff.mpr
      ⟨ha2,fun he => hane (Subtype.ext he)⟩
    have hqa : orderOf (q.symm a) = 2 := (q.symm.orderOf_eq a).trans ha
    have he : (sourceAction F hk).representation (q.symm a) = F.terminalRepresentation a := by
      change F.terminalRepresentation (q (q.symm a)) = _
      rw [q.apply_symm_apply]
    have hr' : (sourceAction F hk).movedRank (q.symm a) ≤ 2 := by
      change finrank (ZMod 2) (LinearMap.range
        ((sourceAction F hk).representation (q.symm a) - LinearMap.id)) ≤ 2
      have heR : (sourceAction F hk).moved (q.symm a) =
          LinearMap.range (F.terminalRepresentation a - LinearMap.id) := by
        simp only [RankCore.SourceAction.moved, he]
      exact (LinearEquiv.ofEq _ _ heR).finrank_eq.le.trans hr
    have hm' : hatSpace F (F.Vi 2) ≤ (sourceAction F hk).moved (q.symm a) := by
      rw [← hline]
      apply Submodule.span_le.mpr
      intro z hz
      have hz : z = v := hz
      rw [hz]
      change v ∈ LinearMap.range ((sourceAction F hk).representation (q.symm a) - LinearMap.id)
      rw [he]
      exact hm
    rcases sourceAction_rank_obstruction F hk
        (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
        models (q.symm a) hqa with hrank | ⟨_,hout⟩
    · omega
    · exact (hout hm').elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

end
