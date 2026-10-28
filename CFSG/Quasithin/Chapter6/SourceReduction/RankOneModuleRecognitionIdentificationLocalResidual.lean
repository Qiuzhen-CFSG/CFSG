module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNormalizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalClosure
public import Theory.GroupAction.FixedIndexTwoResidual
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# Residual centralization and the literal quotient-action kernel

Assume the order-eight intersection V ∩ O₂(C_G(z)) obtained in source
6.2.11. The local normalizer preserves the flag with orders 2, 4, 8, 16
inside V. A two-perfect actor fixing an index-two subgroup of a two-group
fixes the whole group, so three successive applications show that the
local two-residual centralizes V.

The kernel of the action on U/⟨z⟩ is the actual commutator preimage in
C_G(z). It normalizes Z_S and hence V, so its two-residual centralizes V.
The faithful L-action and uniqueness over LT kill that residual. The
order-eight intersection itself forces C_G(z) outside M. Thus the kernel
is exactly the two-core, with no extra escape or recognition premise.

The Chapter 12 companion supplies the original chosen-module normalizers
and uniqueness. The order-eight assertion remains an obligation of
qt-d-1222-recognition-local-analysis; this file proves its consequences,
not the complete LocalAnalysis record. Final identification belongs to
qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, 6.2.9--12, printed pp.685--686.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem centralizes_extension (Y B A : Subgroup G)
    (hY : IsPPerfect 2 Y) (hB : IsPGroup 2 B)
    (_hAB : A ≤ B) (hi : A.relIndex B ≤ 2)
    (hYB : Y ≤ normalizer (B : Set G)) (hYA : Y ≤ centralizer (A : Set G)) :
    Y ≤ centralizer (B : Set G) := by
  let ρ : Y →* MulAut B := B.normalizerMonoidHom.comp (inclusion hYB)
  have hf (y : Y) : ρ y = 1 := by
    apply MulAut.eq_one_of_pPerfect_of_fixed_index_le_two ρ hY hB (A.subgroupOf B) hi
    intro y b hb
    apply Subtype.ext
    change y.val * b.val * y.val⁻¹ = b.val
    rw [← hYA y.property b.val hb, mul_inv_cancel_right]
  intro y hy b hb
  have he := congrArg (fun f : MulAut B => (f ⟨b, hb⟩ : G)) (hf ⟨y, hy⟩)
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem index_le_two_of_cards {A B : Subgroup G} (hAB : A ≤ B)
    (hc : Nat.card B ≤ 2 * Nat.card A) : A.relIndex B ≤ 2 := by
  have he := (A.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv] at he
  change Nat.card A * A.relIndex B = Nat.card B at he
  have hp : 0 < Nat.card A := Nat.card_pos
  nlinarith

variable {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Source 6.2.12(1), derived from the order-eight intersection and its invariant flag. -/
theorem local_residual_centralizes_of_core_card
    (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L R))
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8) :
    (pResidual 2 (centralizer ({z} : Set G) ⊓ M : Subgroup G)).map
      (centralizer ({z} : Set G) ⊓ M).subtype ≤ centralizer (layer L R : Set G) := by
  let H := centralizer ({z} : Set G)
  let I := H ⊓ M
  let Y := (pResidual 2 I).map I.subtype
  let B := layer L R
  let S := ZS (T : Subgroup G) L R
  let A := B ⊓ H.pCoreIn 2
  have hY : IsPPerfect 2 Y := isPPerfect_embedded_pResidual 2 I
  have hYI : Y ≤ I := map_subtype_le _
  have hIB : I ≤ normalizer (B : Set G) :=
    (local_layer_normalizer hE hz ho).symm.le.trans inf_le_right
  have hIS : I ≤ normalizer (S : Set G) :=
    (local_plane_normalizer h hnatural hE hz ho hplane).symm.le.trans inf_le_right
  have hIA : I ≤ normalizer (A : Set G) :=
    (le_inf hIB (inf_le_left.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))).trans
      inf_normalizer_le_normalizer_inf
  have hZS : zpowers z ≤ S := zpowers_le.mpr hz
  have hSA : S ≤ A := le_inf inf_le_left
    (((ZS_le_sourceClosure_intersection h hz).trans inf_le_left).trans
      (local_closure_core h hnatural hz ho hT).1)
  have hS : Nat.card S = 4 := (h.natural_ZS_geometry hnatural).2.1
  have hZ : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, ho]
  have hpB : IsPGroup 2 B := T.isPGroup'.to_le h.layer_le_T
  have hYC : Y ≤ centralizer (zpowers z : Set G) := by
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hYI hy).1
  have hYS : Y ≤ centralizer (S : Set G) := centralizes_extension Y S (zpowers z)
    hY (hpB.to_le inf_le_left) hZS
    (index_le_two_of_cards hZS (by rw [hS, hZ])) (hYI.trans hIS) hYC
  have hYA : Y ≤ centralizer (A : Set G) := centralizes_extension Y A S
    hY (hpB.to_le inf_le_left) hSA
    (index_le_two_of_cards hSA (by rw [hcard, hS]))
    (hYI.trans hIA) hYS
  exact centralizes_extension Y B A hY hpB inf_le_left
    (index_le_two_of_cards inf_le_left (by rw [hnatural.2.1.card, hcard]; decide))
    (hYI.trans hIB) hYA

omit [Finite G] in
private theorem local_closure_normalized (T L R : Subgroup G) (z : G) :
    centralizer ({z} : Set G) ≤ normalizer (sourceClosure T L R z : Set G) := by
  have hh := (M22Recognition.CentralizerExtension.sourceEight
    ((ZS T L R).subgroupOf (centralizer ({z} : Set G)))).le_normalizer_map
      (centralizer ({z} : Set G)).subtype
  simpa only [sourceClosure, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- The order-eight core intersection forces the actual involution centralizer
outside M, without assuming the earlier omega-centralizer escape. -/
theorem local_centralizer_not_le_of_core_card
    (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L R))
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hcard : Nat.card (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8) :
    ¬ centralizer ({z} : Set G) ≤ M := by
  intro hHM
  have hnorm : centralizer ({z} : Set G) ≤ normalizer (layer L R : Set G) := by
    have he := local_layer_normalizer hE hz ho
    rw [inf_eq_left.mpr hHM] at he
    exact he.symm.le.trans inf_le_right
  have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le h.layer_le_T)
    (layer_le_involution_centralizer h hz) hnorm
  rw [inf_eq_left.mpr hcore, hnatural.2.1.card] at hcard
  norm_num at hcard

/-- Source 6.2.12(2) on the literal action U/⟨z⟩. The numerical conclusion
of 6.2.11 is the only remaining local-analysis premise. -/
theorem local_action_kernel_of_core_card
    (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L R))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8) :
    ∀ x ∈ centralizer ({z} : Set G),
      (∀ u ∈ sourceClosure (T : Subgroup G) L R z, ⁅x, u⁆ ∈ zpowers z) ↔
        x ∈ (centralizer ({z} : Set G)).pCoreIn 2 := by
  let H := centralizer ({z} : Set G)
  let U := sourceClosure (T : Subgroup G) L R z
  let Z := zpowers z
  let B := layer L R
  let K := commutatorPreimage H U Z
  let Y := (pResidual 2 K).map K.subtype
  have hHZ : H ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hHN : H ≤ normalizer (Z : Set G) := hHZ.trans (Subgroup.centralizer_le_normalizer _)
  have hKH : K ≤ H := commutatorPreimage_le H U Z
  have hHK : H ≤ normalizer (K : Set G) := commutatorPreimage_normalized H U Z H hHN
    H.le_normalizer (local_closure_normalized _ _ _ _) hHN
  have hKN : K ≤ normalizer (ZS (T : Subgroup G) L R : Set G) := by
    intro x hx
    exact local_action_kernel_normalizes_plane h hz
      ((mem_commutatorPreimage_iff H U Z hHN x).mp hx).2
  have hKI : K ≤ H ⊓ M := le_inf hKH (hKN.trans (hplane.trans hE.normalizer_le))
  have hYK : Y ≤ K := map_subtype_le _
  have hHY : H ≤ normalizer (Y : Set G) := hHK.trans
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hYC : Y ≤ centralizer (B : Set G) := (embedded_pResidual_mono 2 hKI).trans
    (local_residual_centralizes_of_core_card h hnatural hE hz ho hT hplane hcard)
  have hNL : normalizer (B : Set G) ≤ normalizer (L : Set G) :=
    hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  have hLN : L ≤ normalizer (B : Set G) := by
    obtain ⟨F, _, _, _, _, hm⟩ := hnatural.2.1
    exact hm.normalizes
  have hLC : ⁅L, centralizer (B : Set G)⁆ ≤ L.pCoreIn 2 := by
    apply le_trans (le_inf ?_ ?_) (natural_centralizer_eq_core hnatural.2.1).le
    · exact le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.centralizer_le_normalizer _).trans hNL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (hLN.trans (normalizer_le_normalizer_centralizer B))
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQH : L.pCoreIn 2 ≤ H := by
    have hm := pCoreIn_mono_of_normalizes (p := 2) (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer h.sylow_normalizes_L)
    obtain ⟨P, hP⟩ := h.local_mem.1.prop.2.1
    exact hm.trans (((pCoreIn_le_sylow _ P).trans_eq hP).trans hT)
  have hLY : L ≤ normalizer (Y : Set G) := normalizes_residual_of_commutator_le_two
    L H K (L.pCoreIn 2) hHK hQH (isPGroup_pCoreIn 2 L) hLQ
    ((commutator_mono le_rfl hYC).trans hLC)
  have hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2 :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
      (isTwoLocal_involution_centralizer ho) hT
  have hYbot : Y = ⊥ := normal_eq_bot_of_unique_core (L ⊔ (T : Subgroup G)) H M Y
    hunique (local_centralizer_not_le_of_core_card h hnatural hE hz ho hcard)
    hself (hYK.trans hKH) hHY (sup_le hLY (hT.trans hHY))
  have hres : pResidual 2 K = ⊥ :=
    (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hYbot
  have hp : IsPGroup 2 K := (isPGroup_quotient_pResidual (G := K) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 K)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hres])
  have hcore : K ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes hp hKH hHK
  intro x hx
  exact ⟨fun hxu => hcore ((mem_commutatorPreimage_iff H U Z hHN x).mpr ⟨hx, hxu⟩),
    local_core_action_kernel h hnatural hz ho hT⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
