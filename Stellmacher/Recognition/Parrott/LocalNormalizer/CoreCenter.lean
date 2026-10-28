module

public import Stellmacher.Recognition.Parrott.NormalizerCoreCenter
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreCenter`.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The center of the actual normalizer core lies in the actual E∩F. -/
public theorem normalizer_core_center_le_inf_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    (center K).map (N.subtype.comp K.subtype) ≤ E ⊓ d.F := by
  intro H E N K
  let B := (pCore 2 H).map H.subtype
  let X := K.map N.subtype
  have hXcard : Nat.card X = 1024 :=
    (card_map_of_injective N.subtype_injective).trans
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  have hBT : B ≤ (d.sylow : Subgroup G) := by
    rw [d.sylow_map]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal d.localSylow)
  have hBcard : Nat.card B = 512 :=
    (card_map_of_injective H.subtype_injective).trans h.core_card
  have hindex : B.relIndex (d.sylow : Subgroup G) = 4 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) B
      (d.sylow : Subgroup G) bot_le hBT
    rw [relIndex_bot_left, relIndex_bot_left, hBcard, d.sylow_card h] at hc
    omega
  have hindexX : B.relIndex X ≤ 4 :=
    (relIndex_le_of_le_right d.normalizer_core_le_sylow
      (show B.relIndex (d.sylow : Subgroup G) ≠ 0 by rw [hindex]; decide)).trans_eq hindex
  intro b hb
  refine ⟨?_, d.normalizer_core_center_le hb⟩
  by_contra hbE
  have hbB : b ∈ B := d.le_core (d.normalizer_core_center_le hb)
  have hcentral : X ≤ centralizer ({b} : Set G) := by
    obtain ⟨bK, hbK, rfl⟩ := hb
    rintro x ⟨xN, hxK, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (N.subtype.comp K.subtype) (mem_center_iff.mp hbK ⟨xN, hxK⟩))
  have hsmall := parrott_core_element_centralizer_card_le_sixty_four z h b hbB hbE
  have hc := card_le_centralizer_card_mul_relIndex X B ({b} : Set G) hcentral
  have hbound := hc.trans (Nat.mul_le_mul hsmall hindexX)
  rw [hXcard] at hbound
  omega

/-- Choose a conjugate t of z in E∩F, independent of z, generating Z(K)
with z. The conjugator is retained inside the actual normalizer. -/
public theorem exists_normalizer_core_center_generator_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ t : G, t ∈ E ⊓ d.F ∧ t ∉ zpowers z ∧ orderOf t = 2 ∧
      (∃ g : N, (g : G) * z * (g : G)⁻¹ = t) ∧ IsConj z t ∧
      (center K).map (N.subtype.comp K.subtype) = zpowers z ⊔ zpowers t := by
  classical
  intro H E N K
  let Z := (center K).map K.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  let ZG := (center K).map (N.subtype.comp K.subtype)
  have hZmap : Z.map N.subtype = ZG := map_map _ _ _
  have hZE : ZG ≤ E ⊓ d.F := d.normalizer_core_center_le_inf_of_local_inputs h hlocal hproper
  have hzZG : z ∈ ZG := d.z_mem_normalizer_core_center
  obtain ⟨g, hgN, hgT⟩ := SetLike.exists_of_lt hproper
  let gN : N := ⟨g, hgN⟩
  let t := g * z * g⁻¹
  have htZ : t ∈ ZG := by
    obtain ⟨zN, hzZ, hz⟩ := hZmap.symm ▸ hzZG
    rw [← hZmap]
    refine ⟨gN * zN * gN⁻¹, (inferInstance : Z.Normal).conj_mem zN hzZ gN, ?_⟩
    change g * (zN : G) * g⁻¹ = t
    change (zN : G) = z at hz
    rw [hz]
  have htz : t ≠ z := by
    intro heq
    apply hgT
    rw [← d.normalizer_inf_centralizer h]
    exact ⟨hgN, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq)⟩
  have hconj : IsConj z t := isConj_iff.mpr ⟨g, rfl⟩
  have ht1 : t ≠ 1 := by
    intro heq
    have hz1 := isConj_one_left.mp (heq ▸ hconj)
    have ho := h.involution
    simp [hz1] at ho
  have htoutside : t ∉ zpowers z := by
    intro ht
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at ht
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp ht
    have hnlt := Finset.mem_range.mp hn
    interval_cases n
    · exact ht1 (by simpa using heq.symm)
    · exact htz (by simpa using heq.symm)
  have htE := (hZE htZ).1
  have ht2 := (parrott_derived_noncentral_involution z h t htE htoutside).1
  refine ⟨t, hZE htZ, htoutside, ht2, ⟨gN, rfl⟩, hconj, ?_⟩
  have hle : zpowers z ⊔ zpowers t ≤ ZG :=
    sup_le (zpowers_le.mpr hzZG) (zpowers_le.mpr htZ)
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hZcard : Nat.card ZG = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.2.2
  have hpair := parrott_derived_pair_card z h t htE htoutside
  rw [show ({z, t} : Set G) = {z} ∪ {t} from rfl, Subgroup.closure_union,
    ← zpowers_eq_closure, ← zpowers_eq_closure] at hpair
  exact hZcard.le.trans hpair.ge

/-- Every generator of Z(K) independent of z has K as its centralizer in T. -/
public theorem normalizer_core_eq_sylow_centralizer_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ t : G, t ∈ (center K).map (N.subtype.comp K.subtype) → t ∉ zpowers z →
      K.map N.subtype = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) := by
  intro N K t ht htz
  let X := K.map N.subtype
  let T : Subgroup G := d.sylow
  let C := T ⊓ centralizer ({t} : Set G)
  have hXT : X ≤ T := d.normalizer_core_le_sylow
  have htT : t ∈ T := d.le_sylow (d.normalizer_core_center_le ht)
  have hXC : X ≤ C := by
    refine le_inf hXT ?_
    obtain ⟨tK, htK, rfl⟩ := ht
    rintro x ⟨xN, hxK, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (N.subtype.comp K.subtype) (mem_center_iff.mp htK ⟨xN, hxK⟩))
  have hnot : ¬ T ≤ C := by
    intro hTC
    apply htz
    rw [← d.sylow_center_map h]
    refine ⟨⟨t, htT⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTC x.property).2)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) C T bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, d.sylow_card h] at hc
  have hi : 2 ≤ C.relIndex T := by
    have hne : C.relIndex T ≠ 1 := fun hh => hnot (relIndex_eq_one.mp hh)
    have hpos : C.relIndex T ≠ 0 := by intro hh; rw [hh, mul_zero] at hc; omega
    omega
  have hCcard : Nat.card C ≤ 1024 := by nlinarith
  have hXcard : Nat.card X = 1024 :=
    (card_map_of_injective N.subtype_injective).trans
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  exact eq_of_le_of_card_ge hXC (hCcard.trans_eq hXcard.symm)

end Stellmacher.Recognition.ParrottSecondElementaryData
