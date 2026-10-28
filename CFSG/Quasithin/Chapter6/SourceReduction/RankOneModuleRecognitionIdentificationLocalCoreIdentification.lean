module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalBlockCore
public import Theory.GroupTheory.SylowCentralizerComplement
/-!
# The original two-core in the four-plane branch

The sixteen-element closure offends on the natural layer. Natural-module
recognition therefore identifies its literal action with that of T∩L.
The common centralizer fixes this Sylow action on the elementary local core;
odd-index averaging and C_T(L)=1 then remove the central supplement.
Consequently O₂(LT)=O₂(L)=O₂(M)=V, and T∩L is the product of the original
closure U and V.

Source: Aschbacher--Smith, 6.2.11, printed p.686, the block paragraph.
The later ambient A₇ contradiction and the independent 6.2.7--8 argument
remain separate obligations. No LocalAnalysis or later identification is used.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The original closure has a rank-two offender image on V. -/
theorem four_closure_offender
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    letI := h.layer_elementary
    IsOffender (ChapterE.automizerRepresentation (layer L R))
      (ChapterE.inducedAutomizer (layer L R) (sourceClosure (P : Subgroup G) L R z)) := by
  let := h.layer_elementary
  let U := sourceClosure (P : Subgroup G) L R z
  let B := layer L R
  let S := ZS (P : Subgroup G) L R
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  have hUT : U ≤ (P : Subgroup G) := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact (local_closure_core h hnatural hz ho hP).1.trans hc
  have hUN := hUT.trans h.sylow_normalizes_layer
  have hr : rank (ChapterE.inducedAutomizer B U) = 2 := by
    rw [ChapterE.rank_inducedAutomizer B U hUN]
    change Nat.log 2 ((U ⊓ centralizer (B : Set G)).relIndex U) = 2
    rw [four_closure_action_index h hnatural hz ho hP hplane hcard]
    decide
  have hi : S.relIndex B = 4 := by
    have hc := (S.subgroupOf B).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show S ≤ B from inf_le_left)).toEquiv,
      (h.natural_ZS_geometry hnatural).2.1, hnatural.2.1.card] at hc
    change 4 * S.relIndex B = 2 ^ (2 * 2) at hc
    omega
  refine ⟨⟨?_, ChapterE.inducedAutomizer_elementary B U hUN⟩, ?_⟩
  · intro he
    rw [he, rank, card_bot] at hr
    norm_num at hr
  · rw [ChapterE.fixedCodim_inducedAutomizer B U hUN, hr]
    change Nat.log 2 ((B ⊓ centralizer (U : Set G)).relIndex B) ≤ 2
    rw [four_layer_centralizer_closure h hnatural hz ho hP hplane hcard, hi]
    decide

/-- The closure induces exactly the action of the original component Sylow. -/
theorem four_closure_sylow_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    ChapterE.inducedAutomizer (layer L R) (sourceClosure (P : Subgroup G) L R z) =
      ChapterE.inducedAutomizer (layer L R) ((P : Subgroup G) ⊓ L) := by
  let := h.layer_elementary
  obtain ⟨S, hS⟩ := NaturalAction.offender_lifts_sylow (by decide : 2 ≤ 2)
    hnatural.2.1 hNL (four_closure_offender h hnatural hz ho hP hplane hcard)
  have hUT : sourceClosure (P : Subgroup G) L R z ≤ (P : Subgroup G) := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact (local_closure_core h hnatural hz ho hP).1.trans hc
  obtain ⟨_, _, _, _, _, hm⟩ := hnatural.2.1
  exact hS.trans (NaturalAction.sylow_image_eq_in_two_group hm.normalizes P
    h.sylow_normalizes_L S (hS ▸ map_mono (comap_mono hUT)))

/-- Odd Sylow averaging in the actual elementary core removes the central
supplement. This proves the core identity at the block step of 6.2.11. -/
theorem four_local_core_eq_layer
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    (L ⊔ (P : Subgroup G)).pCoreIn 2 = layer L R := by
  let B := layer L R
  let Q := (L ⊔ (P : Subgroup G)).pCoreIn 2
  let U := sourceClosure (P : Subgroup G) L R z
  let C := (P : Subgroup G) ⊓ centralizer ((U ⊔ B : Subgroup G) : Set G)
  let := h.layer_elementary
  let := four_local_core_elementary h hnatural hz ho hP hplane hcard
  have hQC : (P : Subgroup G) ⊓ centralizer (B : Set G) = Q :=
    sylow_layer_centralizer_eq_core h (hnatural.1 ▸ hnatural.2.1)
  have hCQ : C ≤ Q := (inf_le_inf_left _
    (centralizer_le (show B ≤ U ⊔ B from le_sup_right))).trans_eq hQC
  have hUT : U ≤ (P : Subgroup G) := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact (local_closure_core h hnatural hz ho hP).1.trans hc
  have he := four_closure_sylow_action h hnatural hz ho hP hplane hNL hcard
  have hdisp := four_local_core_commutator_component h hnatural hz ho hP hplane hcard
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow P L h.sylow_normalizes_L
  have hCB : C ≤ B := by
    intro c hc
    have hcQ := hCQ hc
    have hcSyl (s : L) (hs : s ∈ S) : Commute (s : G) c := by
      have hsP : (s : G) ∈ (P : Subgroup G) := by
        have hh : s ∈ (P : Subgroup G).subgroupOf L := hS ▸ hs
        exact hh
      let sN : normalizer (B : Set G) := ⟨s, h.sylow_normalizes_layer hsP⟩
      have hsA : B.normalizerMonoidHom.rangeRestrict sN ∈ ChapterE.inducedAutomizer B U := by
        rw [he]
        exact ⟨sN, ⟨hsP, s.property⟩, rfl⟩
      obtain ⟨u, hu, hus⟩ := hsA
      let q := u⁻¹ * sN
      have hqC : (q : G) ∈ centralizer (B : Set G) := by
        have hk : q ∈ B.normalizerMonoidHom.ker := by
          have hh : B.normalizerMonoidHom.rangeRestrict q = 1 := by
            simp only [q, map_mul, map_inv, hus, inv_mul_cancel]
          exact congrArg Subtype.val hh
        rw [normalizerMonoidHom_ker] at hk
        exact hk
      have hqQ : (q : G) ∈ Q := hQC ▸ ⟨(P : Subgroup G).mul_mem
        ((P : Subgroup G).inv_mem (hUT hu)) hsP, hqC⟩
      have huc : Commute (u : G) c := hc.2 (u : G) (mem_sup_left hu)
      have hqc : Commute (q : G) c := Q.le_centralizer hcQ (q : G) hqQ
      have hh := huc.mul_left hqc
      change Commute ((u : G) * ((u : G)⁻¹ * (s : G))) c at hh
      simpa only [mul_inv_cancel_left] using hh
    obtain ⟨v, hv, hvc⟩ := fixed_coset_of_sylow L B (normalizer_commutator_ge_right R L)
      (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) S c
      (fun l hl => by
        change ⁅l, c⁆ ∈ layer L R
        rw [← hdisp, commutator_comm]
        exact commutator_mem_commutator hl hcQ) hcSyl
    have hone : v * c = 1 := show v * c ∈ (⊥ : Subgroup G) from
      hnatural.2.2.1 ▸ ⟨(P : Subgroup G).mul_mem (h.layer_le_T hv) hc.1, hvc⟩
    rw [eq_inv_of_mul_eq_one_right hone]
    exact B.inv_mem hv
  have hsplit := four_sylow_centralizer_supplement h hnatural hz ho hP hplane hcard
  change (P : Subgroup G) ⊓ centralizer (B : Set G) = B ⊔ C at hsplit
  rw [hQC, sup_eq_left.mpr hCB] at hsplit
  exact hsplit

/-- The same core is intrinsic to L and to its specified overgroup M. -/
theorem four_component_and_maximal_core_eq_layer
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    L.pCoreIn 2 = layer L R ∧ M.pCoreIn 2 = layer L R := by
  have hQ := four_local_core_eq_layer h hnatural hz ho hP hplane hNL hcard
  have hLB : L.pCoreIn 2 = layer L R := by
    apply le_antisymm
    · exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (P : Subgroup G) from le_sup_left)
        (sup_le L.le_normalizer h.sylow_normalizes_L)).trans_eq hQ
    · rw [← natural_centralizer_eq_core hnatural.2.1]
      let := h.layer_elementary
      exact le_inf h.layer_le_L (layer L R).le_centralizer
  have hMN : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  have hXM : L ⊔ (P : Subgroup G) ≤ M := sup_le h.L_le h.sylow_le
  have hcoreT : M.pCoreIn 2 ≤ (P : Subgroup G) := by
    have hh := pCoreIn_le_sylow M (P.subtype h.sylow_le)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.sylow_le] at hh
  refine ⟨hLB, le_antisymm ?_ ?_⟩
  · rw [← hQ]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) (hcoreT.trans le_sup_right)
      (hXM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  · rw [← hLB]
    exact pCoreIn_mono_of_normalizes h.L_le hMN

/-- The actual closure and the original natural layer generate T∩L. -/
theorem four_component_sylow_eq_sup
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    (P : Subgroup G) ⊓ L = sourceClosure (P : Subgroup G) L R z ⊔ layer L R := by
  let U := sourceClosure (P : Subgroup G) L R z
  let B := layer L R
  let A := (P : Subgroup G) ⊓ L
  have hUT : U ≤ (P : Subgroup G) := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact (local_closure_core h hnatural hz ho hP).1.trans hc
  have hQ : (P : Subgroup G) ⊓ centralizer (B : Set G) = B :=
    (sylow_layer_centralizer_eq_core h (hnatural.1 ▸ hnatural.2.1)).trans
      (four_local_core_eq_layer h hnatural hz ho hP hplane hNL hcard)
  have he := four_closure_sylow_action h hnatural hz ho hP hplane hNL hcard
  have hBA : B ≤ A := le_inf h.layer_le_T h.layer_le_L
  have hrelative (X Y : Subgroup G) (hXT : X ≤ (P : Subgroup G))
      (hYT : Y ≤ (P : Subgroup G))
      (hXY : ChapterE.inducedAutomizer B X = ChapterE.inducedAutomizer B Y) :
      X ≤ Y ⊔ B := by
    intro x hx
    let xN : normalizer (B : Set G) := ⟨x, h.sylow_normalizes_layer (hXT hx)⟩
    have hxA : B.normalizerMonoidHom.rangeRestrict xN ∈ ChapterE.inducedAutomizer B Y := by
      rw [← hXY]
      exact ⟨xN, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hxA
    let q := y⁻¹ * xN
    have hqC : (q : G) ∈ centralizer (B : Set G) := by
      have hk : q ∈ B.normalizerMonoidHom.ker := by
        have hh : B.normalizerMonoidHom.rangeRestrict q = 1 := by
          simp only [q, map_mul, map_inv, hyx, inv_mul_cancel]
        exact congrArg Subtype.val hh
      rw [normalizerMonoidHom_ker] at hk
      exact hk
    have hqB : (q : G) ∈ B := hQ.le ⟨(P : Subgroup G).mul_mem
      ((P : Subgroup G).inv_mem (hYT hy)) (hXT hx), hqC⟩
    have hh := (Y ⊔ B).mul_mem (mem_sup_left hy) (mem_sup_right hqB)
    change (y : G) * ((y : G)⁻¹ * x) ∈ _ at hh
    simpa only [mul_inv_cancel_left] using hh
  exact le_antisymm (hrelative A U inf_le_left hUT he.symm)
    (sup_le ((hrelative U A hUT inf_le_left he).trans_eq (sup_eq_left.mpr hBA)) hBA)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
