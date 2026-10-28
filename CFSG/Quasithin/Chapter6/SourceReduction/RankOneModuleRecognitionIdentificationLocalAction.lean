module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalClosure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNormalizers
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The original central-quotient action before the numerical conclusion

Inside H = C_G(z), the central line Z = ⟨z⟩ is normal. The normal closure
of the image of Z_S in H/Z is exactly the image of the original U. Its
conjugation action has the literal commutator-preimage kernel. G.2.2 proves
this closure two-reduced, so the full faithful action image has trivial
two-core, without the later 6.2.12 kernel equality.

The action kernel normalizes Z_S and hence V. Thus V intersected with the
kernel is a normal two-subgroup of that kernel and lies in O₂(H). The
reverse inclusion on V follows from the already proved core commutator
bound. These are the independent inputs for the numerical argument.

Source: Aschbacher--Smith, 6.2.10(2--3), printed p.685, using G.2.2, p.332.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace LocalQuotientAction
variable {G : Type*} [Group G]

abbrev Centralizer (z : G) := centralizer ({z} : Set G)

def line (z : G) : Subgroup (Centralizer z) := (zpowers z).subgroupOf (Centralizer z)

theorem line_central (z : G) : line z ≤ center (Centralizer z) := by
  intro x hx
  apply mem_center_iff.mpr
  intro a
  apply Subtype.ext
  have hc : zpowers z ≤ centralizer ({(a : G)} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp a.property).symm)
  exact (mem_centralizer_singleton_iff.mp (hc hx)).symm

instance line_normal (z : G) : (line z).Normal := ⟨by
  intro x hx a
  have hc := mem_center_iff.mp (line_central z hx) a
  simpa only [hc, mul_inv_cancel_right] using hx⟩

abbrev SpaceAmbient (z : G) := Centralizer z ⧸ line z

def projection (z : G) : Centralizer z →* SpaceAmbient z := QuotientGroup.mk' (line z)

def space (T L R : Subgroup G) (z : G) : Subgroup (SpaceAmbient z) :=
  normalClosure (((ZS T L R).subgroupOf (Centralizer z)).map (projection z) : Set (SpaceAmbient z))

instance space_normal (T L R : Subgroup G) (z : G) : (space T L R z).Normal :=
  normalClosure_normal

def action (T L R : Subgroup G) (z : G) : Centralizer z →* MulAut (space T L R z) :=
  (MulAut.conjNormal : SpaceAmbient z →* MulAut (space T L R z)).comp (projection z)

def kernel (T L R : Subgroup G) (z : G) : Subgroup G :=
  commutatorPreimage (Centralizer z) (sourceClosure T L R z) (zpowers z)

theorem closure_normalized (T L R : Subgroup G) (z : G) :
    Centralizer z ≤ normalizer (sourceClosure T L R z : Set G) := by
  have hh := (M22Recognition.CentralizerExtension.sourceEight
    ((ZS T L R).subgroupOf (Centralizer z))).le_normalizer_map (Centralizer z).subtype
  simpa only [sourceClosure, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh

theorem centralizes_line (z : G) : Centralizer z ≤ centralizer (zpowers z : Set G) := by
  apply le_centralizer_iff.mp
  apply zpowers_le.mpr
  intro x hx
  exact mem_centralizer_singleton_iff.mp hx

theorem normalizes_line (z : G) : Centralizer z ≤ normalizer (zpowers z : Set G) :=
  (centralizes_line z).trans (Subgroup.centralizer_le_normalizer _)

theorem kernel_normalized (T L R : Subgroup G) (z : G) :
    Centralizer z ≤ normalizer (kernel T L R z : Set G) :=
  commutatorPreimage_normalized _ _ _ _ (normalizes_line z)
    (Centralizer z).le_normalizer (closure_normalized T L R z) (normalizes_line z)

theorem mem_kernel (T L R : Subgroup G) (z x : G) :
    x ∈ kernel T L R z ↔ x ∈ Centralizer z ∧
      ∀ u ∈ sourceClosure T L R z, ⁅x, u⁆ ∈ zpowers z :=
  mem_commutatorPreimage_iff _ _ _ (normalizes_line z) x

theorem closure_image (T L R : Subgroup G) (z : G) :
    ((sourceClosure T L R z).subgroupOf (Centralizer z)).map (projection z) =
      space T L R z := by
  have hc : (sourceClosure T L R z).subgroupOf (Centralizer z) =
      normalClosure ((ZS T L R).subgroupOf (Centralizer z) : Set (Centralizer z)) := by
    exact (normalClosure ((ZS T L R).subgroupOf (Centralizer z) : Set (Centralizer z))).comap_map_eq_self_of_injective
      (Centralizer z).subtype_injective
  rw [hc]
  exact map_normalClosure _ (projection z) (QuotientGroup.mk'_surjective _)

theorem action_ker (T L R : Subgroup G) (z : G) :
    (action T L R z).ker = (kernel T L R z).subgroupOf (Centralizer z) := by
  ext x
  rw [MonoidHom.mem_ker, action, MonoidHom.comp_apply,
    ← MonoidHom.mem_ker, MulAut.conjNormal_ker_eq_centralizer, ← closure_image]
  constructor
  · intro hx
    apply (mem_kernel T L R z x).mpr
    refine ⟨x.property, ?_⟩
    intro u hu
    have huH : u ∈ Centralizer z := map_subtype_le _ hu
    have hc := hx _ (mem_map_of_mem (projection z) (show (⟨u, huH⟩ : Centralizer z) ∈
      (sourceClosure T L R z).subgroupOf (Centralizer z) from hu))
    have he : projection z ⁅x, (⟨u, huH⟩ : Centralizer z)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc.symm
    exact (QuotientGroup.eq_one_iff (N := line z) _).mp he
  · intro hx
    have hh := (mem_kernel T L R z x).mp hx
    rintro _ ⟨u, hu, rfl⟩
    have he : projection z ⁅x, u⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hh.2 u hu)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at he
    exact he.symm

variable [Finite G] {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem reduced_space (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z) :
    IsPReduced 2 (space (T : Subgroup G) L R z) := by
  let H := Centralizer z
  let S := (ZS (T : Subgroup G) L R).subgroupOf H
  have hSH : ZS (T : Subgroup G) L R ≤ H := h.ZS_le_T.trans hT
  have hZH : zpowers z ≤ H := (zpowers_le.mpr hz).trans hSH
  have hZcard : Nat.card (line z) = 2 := by
    change Nat.card ((zpowers z).subgroupOf H) = 2
    rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv, Nat.card_zpowers, ho]
  have hScard : Nat.card S = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv).trans (h.natural_ZS_geometry hnatural).2.1
  have hZS : line z ≤ S := comap_mono (zpowers_le.mpr hz)
  have hSe : IsElementaryAbelian 2 S := by
    let := h.ZS_elementary
    exact IsElementaryAbelian.subgroupOf hSH
  let P := T.subtype hT
  have hPS : (P : Subgroup H) ≤ normalizer (S : Set H) := by
    rw [← subgroupOf_normalizer_eq hSH]
    exact comap_mono h.sylow_normalizes_ZS
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) (isTwoLocal_involution_centralizer ho) hT)
  have hk : (projection z).ker = line z := QuotientGroup.ker_mk' _
  apply isPReduced_normalClosure_image_of_irreducible (projection z)
    (QuotientGroup.mk'_surjective _) S (P : Subgroup H) P hchar hSe
  · rwa [hk]
  · intro he
    have hc := hZcard
    rw [hk] at he
    rw [he, hScard] at hc
    contradiction
  · exact comap_mono h.ZS_le_T
  · exact le_rfl
  · exact hPS
  · intro E hZE hES _
    rw [hk] at hZE ⊢
    change E ≤ S at hES
    have hlow : 2 ≤ Nat.card E := hZcard ▸ card_le_of_le hZE
    have hdvd : Nat.card E ∣ 2 ^ 2 := by
      calc
        Nat.card E ∣ Nat.card S := card_dvd_of_le hES
        _ = 2 ^ 2 := hScard
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hec : Nat.card E = 2 ∨ Nat.card E = 4 := by
      interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
    rcases hec with hec | hec
    · exact Or.inl (eq_of_le_of_card_ge hZE (by omega)).symm
    · exact Or.inr (eq_of_le_of_card_ge hES (by rw [hScard, hec]))

theorem action_range_core (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z) :
    pCore 2 (action (T : Subgroup G) L R z).range = ⊥ := by
  let W := space (T : Subgroup G) L R z
  let f : SpaceAmbient z →* MulAut W := MulAut.conjNormal
  have hred := reduced_space h hnatural hz ho hT
  have hr : (action (T : Subgroup G) L R z).range = f.range := by
    rw [action, MonoidHom.range_comp,
      (projection z).range_eq_top_of_surjective (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  rw [hr]
  let e : (SpaceAmbient z ⧸ centralizer (W : Set (SpaceAmbient z))) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq (MulAut.conjNormal_ker_eq_centralizer W).symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  rw [← pCore_map_iso 2 e, hred.quotient_pCore_eq_bot, Subgroup.map_bot]

theorem layer_inf_kernel (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G)) :
    layer L R ⊓ kernel (T : Subgroup G) L R z = layer L R ⊓ (Centralizer z).pCoreIn 2 := by
  let K := kernel (T : Subgroup G) L R z
  have hKH : K ≤ Centralizer z := commutatorPreimage_le _ _ _
  have hKN : K ≤ normalizer (layer L R : Set G) := by
    intro x hx
    exact hplane (local_action_kernel_normalizes_plane h hz
      ((mem_kernel (T : Subgroup G) L R z x).mp hx).2)
  have hKI : K ≤ normalizer (layer L R ⊓ K : Set G) :=
    (le_inf hKN K.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hcore : layer L R ⊓ K ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((T.isPGroup'.to_le h.layer_le_T).to_le inf_le_left)
      inf_le_right hKI
  apply le_antisymm
  · exact le_inf inf_le_left (hcore.trans
      (pCoreIn_mono_of_normalizes hKH (kernel_normalized _ _ _ _)))
  · intro x hx
    exact ⟨hx.1, (mem_kernel _ _ _ _ x).mpr ⟨pCoreIn_le 2 _ hx.2,
      local_core_action_kernel h hnatural hz ho hT hx.2⟩⟩

end LocalQuotientAction
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
