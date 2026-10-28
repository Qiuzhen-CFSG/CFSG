module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.ResidualSpan
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.SylowThompson
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PcQuotient.ResidualAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PcQuotient.GeometryInput
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Marked
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The first marked factor of the original line quotient

This file records the short calculation immediately after 15.3.66.  The
ambient two-core of `M_c` is intersected with the original line normalizer,
and retains a conditional helper for restricting commutators to that
intersection. The source obtains nontrivial action on `E` from the central
involution in the Sylow action image; it does not assert the reverse
containment for the commutator with `Z_S`. No assertion from 15.3.67 is used.

The full residual commutator is proved from nontrivial action on `E`, and
both mixed commutators are placed inside the original `Q_E`. The fixed
subgroup of an escaping element is determined from the source orders and
`M_c=C_G(Z)`. The finite Sylow movement calculation and the construction
of compatible quotient coordinates remain separate prerequisites. The
quotient uses the actual image of `C_G(E)`, without assigning its type.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.49(2) and 15.3.66, printed pp.1142 and 1152–1153
(PDF pp.1159 and 1169–1170).
-/

@[expose] public section

open Subgroup Stellmacher
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

variable {G : Type*} [Group G]

/-! ## Restricting the 15.3.49(2) commutator -/

/- The ambient definition is intentionally unfolded here: both
`twoCoreAmbient Mc` and `Mc.pCoreIn 2` are the image of the same intrinsic
core under `Mc.subtype`. -/
theorem linePc_le_pCoreIn (Mc E : Subgroup G) :
    linePc Mc E ≤ Mc.pCoreIn 2 := by
  change Stellmacher.twoCoreAmbient Mc ⊓ lineNormalizer E ≤ _
  exact inf_le_left

/-!
If the selected line geometry gives `Z ≤ [Z_S,P_c]`, then the equality
`[Z_S,O₂(M_c)] = Z` from 15.3.49(2) restricts to the actual `P_c`.
-/
theorem linePc_commutator_eq_of_source (Mc E Zs Z : Subgroup G)
    (h49 : ⁅Zs, Mc.pCoreIn 2⁆ = Z)
    (hgeom : Z ≤ ⁅Zs, linePc Mc E⁆) :
    ⁅Zs, linePc Mc E⁆ = Z := by
  apply le_antisymm
  · calc
      ⁅Zs, linePc Mc E⁆ ≤ ⁅Zs, Mc.pCoreIn 2⁆ :=
        commutator_mono le_rfl (linePc_le_pCoreIn Mc E)
      _ = Z := h49
  · exact hgeom

/-! A nontrivial source commutator forces `P_c` to move the fixed line. -/
theorem linePc_not_le_centralizer (Mc E Zs Z : Subgroup G)
    (hcomm : ⁅Zs, linePc Mc E⁆ = Z) (hZ : Z ≠ ⊥) :
    ¬ linePc Mc E ≤ centralizer (Zs : Set G) := by
  intro hle
  apply hZ
  apply le_bot_iff.mp
  rw [← hcomm]
  apply commutator_le.mpr
  intro z hz p hp
  have hc := (mem_centralizer_iff.mp (hle hp)) z hz
  simp only [commutatorElement_def]
  rw [hc]
  simp

/-! An alternative conditional criterion: if `S_E` centralizes `Z_S`,
nontrivial action on `Z_S` forces `P_c` to escape `S_E`.
The source route instead uses nontrivial action on `E`. -/
theorem linePc_not_le_lineS (Mc Y T E Zs Z : Subgroup G)
    (hcomm : ⁅Zs, linePc Mc E⁆ = Z) (hZ : Z ≠ ⊥)
    (hS : lineS Y T E ≤ centralizer (Zs : Set G)) :
    ¬ linePc Mc E ≤ lineS Y T E := by
  intro hle
  exact linePc_not_le_centralizer Mc E Zs Z hcomm hZ
    (hle.trans hS)

/-- In the source route it is the action on `E` that detects escape from
the kernel `S_E` in 15.3.66(5). -/
theorem linePc_not_le_lineS_of_noncentral (Mc Y T E : Subgroup G)
    (hnot : ¬ linePc Mc E ≤ lineC E)
    (hkernel : lineS Y T E = (lineY Y E ⊔ lineT T E) ⊓ lineC E) :
    ¬ linePc Mc E ≤ lineS Y T E := by
  intro hle
  exact hnot (hle.trans (hkernel.trans_le inf_le_right))

/-! The escaping element is selected in the genuine `P_c`, before any
quotient is introduced. -/
theorem exists_tau_linePc (Mc Y T E : Subgroup G)
    (hnot : ¬ linePc Mc E ≤ lineS Y T E)
    (hPcT : linePc Mc E ≤ lineT T E) :
    ∃ τ : G, τ ∈ linePc Mc E ∧ τ ∉ lineS Y T E ∧ τ ∈ lineT T E := by
  obtain ⟨τ, hτ, hτS⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨τ, hτ, hτS, hPcT hτ⟩

theorem tau_not_centralizer_of_lineS_eq_centralizer
    (Y T E : Subgroup G) (τ : G)
    (hS : lineS Y T E = T ⊓ lineC E)
    (hτT : τ ∈ lineT T E) (hτS : τ ∉ lineS Y T E) :
    τ ∉ lineC E := by
  intro hτC
  apply hτS
  rw [hS]
  exact ⟨hτT.1, hτC⟩

/-! ## The original residual and the Sylow centralizer -/

theorem lineY_residual_and_normal [Finite G] (Mc Y T E : Subgroup G)
    (hTMc : T ≤ Mc) (hCMc : lineC E ≤ Mc)
    (hcore : twoCoreAmbient Mc ≤ T) (hTY : T ≤ normalizer (Y : Set G))
    (hprod : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (lineC E : Set G))
    (hcomm : lineY Y E = ⁅lineY Y E, linePc Mc E⁆) :
    lineY Y E = twoResidualAmbient (conjugateSpanBy (linePc Mc E)
      (lineNormalizer E)) ∧
      ((lineY Y E).subgroupOf (lineNormalizer E)).Normal := by
  exact ⟨lineY_eq_residual_span Mc Y T E hTMc hCMc hcore hTY hprod hcomm,
    lineY_normal_of_commutator Mc Y T E hTMc hCMc hcore hTY hprod hcomm⟩

theorem lineS_and_centralizer_sylow [Finite G] (Y T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype =
      lineT T E)
    (hkernel : lineS Y T E = (lineY Y E ⊔ lineT T E) ⊓ lineC E) :
    lineS Y T E = T ⊓ lineC E ∧
      ∃ P : Sylow 2 (lineC E),
        (P : Subgroup (lineC E)).map (lineC E).subtype = T ⊓ lineC E := by
  exact ⟨lineS_eq_centralizer Y T E U hU hkernel,
    lineC_sylow T E U hU⟩

/-- The centralizer normalizes `P_c`. Its commutators with `P_c` lie both
in the centralizer and in `O₂(M_c)`, hence in its own intrinsic two-core. -/
theorem linePc_commutator_lineC_le_core (Mc E : Subgroup G)
    (hCMc : lineC E ≤ Mc) :
    ⁅linePc Mc E, lineC E⁆ ≤ (lineC E).pCoreIn 2 := by
  have hCN : lineNormalizer E ≤ normalizer (lineC E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (E : Set G))).mp
      inferInstance
  have hPcN : lineC E ≤ normalizer (linePc Mc E : Set G) :=
    (le_inf hCMc (centralizer_le_normalizer (E : Set G))).trans (linePc_normalizer Mc E)
  have hPc : ⁅linePc Mc E, lineC E⁆ ≤ linePc Mc E :=
    le_normalizer_iff_commutator_le_left.mp hPcN
  have hC : ⁅linePc Mc E, lineC E⁆ ≤ lineC E :=
    le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hCN)
  exact (le_inf hC (hPc.trans (linePc_le_pCoreIn Mc E))).trans
    (inf_pCoreIn_le_of_le 2 hCMc)

/-- The original `P_c` and centralizer commute modulo the original `Q_E`. -/
theorem linePc_commutator_lineC_le_lineQ (Mc E : Subgroup G)
    (hCMc : lineC E ≤ Mc) : ⁅linePc Mc E, lineC E⁆ ≤ lineQ E := by
  have hCN : lineNormalizer E ≤ normalizer (lineC E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (E : Set G))).mp
      inferInstance
  exact (linePc_commutator_lineC_le_core Mc E hCMc).trans
    (pCoreIn_mono_of_normalizes (centralizer_le_normalizer (E : Set G)) hCN)

/-- After relative normality is established, 15.3.49(3) puts the mixed
commutator in the intrinsic core of `Y_E`: the centralizer fixes `Z ≤ E`. -/
theorem lineY_commutator_lineC_le_core (Y E Z : Subgroup G) (hZE : Z ≤ E)
    (hYcore : Y.pCoreIn 2 = Y ⊓ centralizer (Z : Set G))
    (hYn : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal) :
    ⁅lineY Y E, lineC E⁆ ≤ (lineY Y E).pCoreIn 2 := by
  have hYLE : lineY Y E ≤ lineNormalizer E := (lineY_le Y E).trans inf_le_right
  have hYLY : lineY Y E ≤ Y := (lineY_le Y E).trans inf_le_left
  have hYN := (normal_subgroupOf_iff_le_normalizer hYLE).mp hYn
  have hCN : lineNormalizer E ≤ normalizer (lineC E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (E : Set G))).mp
      inferInstance
  have hY : ⁅lineY Y E, lineC E⁆ ≤ lineY Y E :=
    le_normalizer_iff_commutator_le_left.mp ((centralizer_le_normalizer (E : Set G)).trans hYN)
  have hC : ⁅lineY Y E, lineC E⁆ ≤ lineC E :=
    le_normalizer_iff_commutator_le_right.mp (hYLE.trans hCN)
  have hc : ⁅lineY Y E, lineC E⁆ ≤ Y.pCoreIn 2 := by
    rw [hYcore]
    exact le_inf (hY.trans hYLY) (hC.trans (centralizer_le hZE))
  exact (le_inf hY hc).trans (inf_pCoreIn_le_of_le 2 hYLY)

/-- The original `Y_E` and centralizer commute modulo the original `Q_E`. -/
theorem lineY_commutator_lineC_le_lineQ (Y E Z : Subgroup G) (hZE : Z ≤ E)
    (hYcore : Y.pCoreIn 2 = Y ⊓ centralizer (Z : Set G))
    (hYn : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal) :
    ⁅lineY Y E, lineC E⁆ ≤ lineQ E := by
  have hYLE : lineY Y E ≤ lineNormalizer E := (lineY_le Y E).trans inf_le_right
  exact (lineY_commutator_lineC_le_core Y E Z hZE hYcore hYn).trans
    (pCoreIn_mono_of_normalizes hYLE ((normal_subgroupOf_iff_le_normalizer hYLE).mp hYn))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification

variable {G : Type*} [Group G]
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

/-! ## Fixed subgroup of the selected escaping element -/

theorem fixed_subgroup_eq_of_card [Finite G]
    (E Z : Subgroup G) (τ : G)
    (hZE : Z ≤ E)
    (hZfix : Z ≤ centralizer ({τ} : Set G))
    (hcard : Nat.card ↥(E ⊓ centralizer ({τ} : Set G)) ≤ Nat.card ↥Z) :
    E ⊓ centralizer ({τ} : Set G) = Z := by
  have hZC : Z ≤ E ⊓ centralizer ({τ} : Set G) := le_inf hZE hZfix
  exact (eq_of_le_of_card_ge hZC hcard).symm

/-- A nontrivial action on a four-group fixing a subgroup of order two
has exactly that fixed subgroup. No fixed-space cardinal bound is assumed. -/
theorem fixed_subgroup_eq_of_noncentral [Finite G]
    (E Z : Subgroup G) (τ : G) (hE : Nat.card E = 4)
    (hZ : Nat.card Z = 2) (hZE : Z ≤ E)
    (hZfix : Z ≤ centralizer ({τ} : Set G)) (hτ : τ ∉ centralizer (E : Set G)) :
    E ⊓ centralizer ({τ} : Set G) = Z := by
  let F := E ⊓ centralizer ({τ} : Set G)
  have hFE : F ≤ E := inf_le_left
  have hne : F ≠ E := by
    intro he
    apply hτ
    intro e heE
    have hf : e ∈ F := he.symm ▸ heE
    exact (hf.2 τ (Set.mem_singleton τ)).symm
  have hle : Nat.card F ≤ 4 := hE ▸ card_le_of_le hFE
  have hlt : Nat.card F < 4 := lt_of_le_of_ne hle (by
    intro he
    exact hne (eq_of_le_of_card_ge hFE (by omega)))
  have hd := card_dvd_of_le hFE
  have hfcard : Nat.card F ≤ 2 := by
    by_contra hn
    have he : Nat.card F = 3 := by omega
    rw [he, hE] at hd
    norm_num at hd
  exact fixed_subgroup_eq_of_card E Z τ hZE hZfix (hZ ▸ hfcard)

/-- The actual escaping element fixes precisely `Z`, using `M_c=C_G(Z)`
and the kernel/Sylow identification of `S_E`. -/
theorem linePc_fixed_subgroup [Finite G]
    (Mc Y T E Z : Subgroup G) (τ : G)
    (hMc : Mc = centralizer (Z : Set G))
    (hE : Nat.card E = 4) (hZ : Nat.card Z = 2) (hZE : Z ≤ E)
    (hS : lineS Y T E = T ⊓ lineC E)
    (hPcT : linePc Mc E ≤ lineT T E)
    (hτ : τ ∈ linePc Mc E) (hτS : τ ∉ lineS Y T E) :
    E ⊓ centralizer ({τ} : Set G) = Z := by
  have hτZ : τ ∈ centralizer (Z : Set G) :=
    hMc ▸ pCoreIn_le 2 Mc (linePc_le_pCoreIn Mc E hτ)
  apply fixed_subgroup_eq_of_noncentral E Z τ hE hZ hZE
  · intro z hz t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact (hτZ z hz).symm
  · exact tau_not_centralizer_of_lineS_eq_centralizer Y T E τ hS (hPcT hτ) hτS

/-- Select `τ` in the original `P_c` and prove the fixation assertion from
the source orders and centralizer equality, without an extra fixation premise. -/
theorem exists_tau_with_fixed_subgroup_of_source [Finite G]
    (Mc Y T E Z : Subgroup G)
    (hMc : Mc = centralizer (Z : Set G))
    (hE : Nat.card E = 4) (hZ : Nat.card Z = 2) (hZE : Z ≤ E)
    (hS : lineS Y T E = T ⊓ lineC E)
    (hPcT : linePc Mc E ≤ lineT T E)
    (hnot : ¬ linePc Mc E ≤ lineS Y T E) :
    ∃ τ : G, τ ∈ linePc Mc E ∧ τ ∉ lineS Y T E ∧ τ ∈ lineT T E ∧
      E ⊓ centralizer ({τ} : Set G) = Z := by
  obtain ⟨τ, hτ, hτS, hτT⟩ := LocalStructure.exists_tau_linePc Mc Y T E hnot hPcT
  exact ⟨τ, hτ, hτS, hτT,
    linePc_fixed_subgroup Mc Y T E Z τ hMc hE hZ hZE hS hPcT hτ hτS⟩

/-! Package the escaping element together with its actual fixed subgroup.  The
two premises below are the elementary four-space fixation calculation: they
are stated for the selected element, so no centralizer of `τ` inside
`C_G(E)` is substituted for the required ambient fixation in `E`. -/
theorem exists_tau_with_fixed_subgroup [Finite G]
    (Mc Y T E Z : Subgroup G)
    (hnot : ¬ linePc Mc E ≤ lineS Y T E)
    (hPcT : linePc Mc E ≤ lineT T E)
    (hZE : Z ≤ E)
    (hfixed : ∀ τ : G, τ ∈ linePc Mc E → τ ∉ lineS Y T E →
      Z ≤ centralizer ({τ} : Set G))
    (hcard : ∀ τ : G, τ ∈ linePc Mc E → τ ∉ lineS Y T E →
      Nat.card ↥(E ⊓ centralizer ({τ} : Set G)) ≤ Nat.card ↥Z) :
    ∃ τ : G, τ ∈ linePc Mc E ∧ τ ∉ lineS Y T E ∧ τ ∈ lineT T E ∧
      E ⊓ centralizer ({τ} : Set G) = Z := by
  obtain ⟨τ, hτ, hτS, hτT⟩ :=
    LocalStructure.exists_tau_linePc Mc Y T E hnot hPcT
  refine ⟨τ, hτ, hτS, hτT, ?_⟩
  exact fixed_subgroup_eq_of_card E Z τ hZE (hfixed τ hτ hτS) (hcard τ hτ hτS)

/-! ## Marking the actual quotient coordinates -/

/-!
The coordinate equivalence is built by the local action calculation.  This
constructor only packages its checked compatibility equations into the public
`MarkedDecomposition` interface; in particular its second coordinate remains
`centralizerImage E`.
-/
noncomputable def markedDecompositionOfCoordinates
    (Y T E : Subgroup G) (τ : G) (hτ : τ ∈ lineT T E)
    (e : (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × centralizerImage E)
    (hfirst :
      (((lineY Y E ⊔ zpowers τ).subgroupOf (lineNormalizer E)).map
        (e.toMonoidHom.comp (quotientMap E))) =
        (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥)
    (hcentral : ∀ c : centralizer (E : Set G),
      e (restrictedQuotient E _ (centralizer_le_normalizer (E : Set G)) c) =
        (1, centralizerImageMap E c)) :
    MarkedDecomposition Y T E :=
  { tau := τ
    tau_mem := hτ
    equiv := e
    first_factor := hfirst
    centralizer_factor := hcentral }

theorem markedDecompositionOfCoordinates_tau
    (Y T E : Subgroup G) (τ : G) (hτ : τ ∈ lineT T E)
    (e : (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × centralizerImage E)
    (hfirst :
      (((lineY Y E ⊔ zpowers τ).subgroupOf (lineNormalizer E)).map
        (e.toMonoidHom.comp (quotientMap E))) =
        (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥)
    (hcentral : ∀ c : centralizer (E : Set G),
      e (restrictedQuotient E _ (centralizer_le_normalizer (E : Set G)) c) =
        (1, centralizerImageMap E c)) :
    (markedDecompositionOfCoordinates Y T E τ hτ e hfirst hcentral).tau = τ ∧
      (markedDecompositionOfCoordinates Y T E τ hτ e hfirst hcentral).tau_mem = hτ :=
  ⟨rfl, rfl⟩

/-! A checked first-coordinate image of `Y_E` is the alternating subgroup. -/
theorem lineY_image_eq_alternating_of_card [Finite G]
    (Y T E : Subgroup G) (d : MarkedDecomposition Y T E)
    (hle :
      ((lineY Y E).subgroupOf (lineNormalizer E)).map
          (d.equiv.toMonoidHom.comp (quotientMap E)) ≤
        (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (centralizerImage E)))
    (hcard : Nat.card
      (((lineY Y E).subgroupOf (lineNormalizer E)).map
          (d.equiv.toMonoidHom.comp (quotientMap E))) = 3) :
    ((lineY Y E).subgroupOf (lineNormalizer E)).map
          (d.equiv.toMonoidHom.comp (quotientMap E)) =
        (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (centralizerImage E)) := by
  apply eq_of_le_of_card_ge hle
  have htarget : Nat.card ↥((alternatingGroup (Fin 3)).prod
      (⊥ : Subgroup (centralizerImage E))) = 3 := by
    calc
      Nat.card ↥((alternatingGroup (Fin 3)).prod
          (⊥ : Subgroup (centralizerImage E))) =
          Nat.card (↥(alternatingGroup (Fin 3)) ×
            ↥(⊥ : Subgroup (centralizerImage E))) :=
        Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv
      _ = Nat.card (alternatingGroup (Fin 3)) *
          Nat.card (⊥ : Subgroup (centralizerImage E)) := Nat.card_prod _ _
      _ = 3 := by
        rw [nat_card_alternatingGroup, Nat.card_fin, Subgroup.card_bot]
        norm_num [Nat.factorial]
  rw [htarget]
  exact hcard.ge

open CFSG.Quasithin.Chapter15.Section03

private theorem residual_first_factor (C : Type*) [Group C] :
    (pResidual 2 ((⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup C))).map
        ((⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup C)).subtype =
      (alternatingGroup (Fin 3)).prod (⊥ : Subgroup C) := by
  let B := (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup C)
  let e : B ≃* Equiv.Perm (Fin 3) :=
    { toFun := fun x => x.val.1
      invFun := fun x => ⟨(x,1), ⟨mem_top _, rfl⟩⟩
      left_inv := fun x => Subtype.ext (Prod.ext rfl x.property.2.symm)
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have he : (pResidual 2 B).map e.toMonoidHom = alternatingGroup (Fin 3) := by
    rw [map_pResidual, Equiv.Perm.twoResidual_eq_alternating]
  change (pResidual 2 B).map B.subtype = _
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨he ▸ mem_map_of_mem e.toMonoidHom hb, b.property.2⟩
  · intro hx
    obtain ⟨b,hb,hbx⟩ := he.symm ▸ hx.1
    exact ⟨b,hb,Prod.ext hbx (b.property.2.trans hx.2.symm)⟩

/-- The marked first factor forces the compatible image of `Y_E` to be
`A₃ × 1`. This is residual functoriality, with no cardinality or image
containment premise: `τ ∈ T_E` is a two-element and normalizes `Y_E`. -/
theorem lineY_image_eq_alternating [Finite G] (Y E : Subgroup G) (T : Sylow 2 G)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (d : MarkedDecomposition Y T E) :
    ((lineY Y E).subgroupOf (lineNormalizer E)).map
        (d.equiv.toMonoidHom.comp (quotientMap E)) =
      (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (centralizerImage E)) := by
  let A := lineY Y E ⊔ zpowers d.tau
  have hTau : zpowers d.tau ≤ lineT T E := zpowers_le.mpr d.tau_mem
  have hYN : lineY Y E ≤ lineNormalizer E := (lineY_le Y E).trans inf_le_right
  have hAN : A ≤ lineNormalizer E := sup_le hYN (hTau.trans inf_le_right)
  have h2 : IsPGroup 2 (zpowers d.tau) := T.isPGroup'.to_le (hTau.trans inf_le_left)
  have hnorm : zpowers d.tau ≤ normalizer (lineY Y E : Set G) :=
    hTau.trans (lineT_le_normalizer_lineY Y T E hTY)
  have hres : twoResidualAmbient A = lineY Y E :=
    SectionsFiveToSeven.twoResidualIn_sup_twoGroup_eq (Y ⊓ lineNormalizer E) _ h2 hnorm
  have hmapres : (pResidual 2 A).map A.subtype = lineY Y E := by
    rw [← ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact hres
  let f := d.equiv.toMonoidHom.comp (quotientMap E)
  let B := A.subgroupOf (lineNormalizer E)
  have hBr : (pResidual 2 B).map B.subtype = (lineY Y E).subgroupOf (lineNormalizer E) := by
    apply map_injective (lineNormalizer E).subtype_injective
    have he := map_embedded_pResidual 2 B (lineNormalizer E).subtype
    rw [map_subgroupOf_eq_of_le hAN] at he
    rw [he, hmapres, map_subgroupOf_eq_of_le hYN]
  rw [← hBr, map_embedded_pResidual]
  have hB : B.map f = (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup (centralizerImage E)) :=
    d.first_factor
  rw [hB]
  exact residual_first_factor _

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification

end
