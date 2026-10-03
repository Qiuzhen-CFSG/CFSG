module

public import Stellmacher.Recognition.Parrott.NormalizerCoreCenter
public import Stellmacher.Recognition.Parrott.DerivedTCentralizerCore
public import Stellmacher.Recognition.Parrott.OuterFourFixedSpace

/-!
# The fixed-space centralizer inside the second normalizer core

For an actual involution y in K=O₂(N_G(F)) outside J=O₂(C_G(z)), put
V=C_E(y), where E is the ambient derived core. The fixed-space calculation
gives |V|=8; the core pairing gives |C_J(V)|=128. The central four-group
of K places C_J(V) inside K. The order-four fixed-space bound then gives
|C_K(V)|=256, and self-centralization of E gives Z(C_K(V))=V.
These computations isolate the remaining involution-generation calculation
needed to identify this centralizer with Ω₁(K).

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677, the structure calculation surrounding Lemma 6.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The derived fixed space of an actual outer involution has order eight. -/
public theorem normalizer_core_outer_fixed_card (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ y : G, y ∈ K.map N.subtype → orderOf y = 2 → y ∉ J.map H.subtype →
      Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) = 8 := by
  intro H J E N K y hy hy2 hyJ
  have hyH : y ∈ H := d.sylow_le_centralizer (d.normalizer_core_le_sylow hy)
  let yH : H := ⟨y, hyH⟩
  have hyH2 : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy2
  have hyHJ : yH ∉ J := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hc := parrott_outer_involution_fixed_card z h yH hyH2 hyHJ
  rw [← card_map_of_injective (K := (centralizer ({y} : Set G)).subgroupOf E)
    E.subtype_injective, subgroupOf_map_subtype, inf_comm] at hc
  exact hc

/-- The fixed-space centralizer is the order-256 candidate for Ω₁(K).
Its intersection with the original core has order 128 and its center is
exactly the eight-element derived fixed space. -/
public theorem normalizer_core_outer_fixed_centralizer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ y : G, y ∈ K.map N.subtype → orderOf y = 2 → y ∉ J.map H.subtype →
      let V := E ⊓ centralizer ({y} : Set G)
      let B := J.map H.subtype ⊓ centralizer (V : Set G)
      let C := K.map N.subtype ⊓ centralizer (V : Set G)
      Nat.card V = 8 ∧ Nat.card B = 128 ∧ B ≤ K.map N.subtype ∧
        Nat.card C = 256 ∧ C = B ⊔ zpowers y ∧ (center C).map C.subtype = V := by
  intro H J E N K y hy hy2 hyJ V B C
  let L := J.map H.subtype
  let M := K.map N.subtype
  have hVcard : Nat.card V = 8 := d.normalizer_core_outer_fixed_card h y hy hy2 hyJ
  have hyH : y ∈ H := d.sylow_le_centralizer (d.normalizer_core_le_sylow hy)
  have hzV : z ∈ V := ⟨d.z_mem_inf.1,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hyH).symm⟩
  have hBcard : Nat.card B = 128 := by
    have hc := parrott_core_inf_centralizer_card z h V (zpowers_le.mpr hzV) inf_le_left
    change Nat.card V * Nat.card B = 1024 at hc
    rw [hVcard] at hc
    omega
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator h hN hproper
  have htZ : t ∈ (center K).map (N.subtype.comp K.subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have htV : t ∈ V := by
    refine ⟨ht.1, ?_⟩
    obtain ⟨tK, htK, rfl⟩ := htZ
    obtain ⟨yN, hyK, rfl⟩ := hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (N.subtype.comp K.subtype) (mem_center_iff.mp htK ⟨yN, hyK⟩)).symm
  have hBM : B ≤ M := by
    rw [show M = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) from
      d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz]
    intro b hb
    exact ⟨d.core_le_sylow hb.1, mem_centralizer_singleton_iff.mpr (hb.2 t htV).symm⟩
  have hBC : B ≤ C := le_inf hBM inf_le_right
  have hyC : y ∈ C := ⟨hy, by
    intro v hv
    exact mem_centralizer_singleton_iff.mp hv.2⟩
  have hLC : L ⊓ C = B := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left hBC
  have hidx : L.relIndex C ≤ 2 :=
    parrott_two_subgroup_centralizer_relIndex_le_two z h C V
      (inf_le_left.trans (d.normalizer_core_le_sylow.trans d.sylow_le_centralizer))
      ((pCore_isPGroup.map N.subtype).to_le inf_le_left)
      inf_le_left hVcard.ge inf_le_right
  have hidxne : L.relIndex C ≠ 1 := by
    intro hh
    exact hyJ (relIndex_eq_one.mp hh hyC)
  have hidxpos : L.relIndex C ≠ 0 := by
    have hc := (L.subgroupOf C).index_mul_card
    have hp : 0 < Nat.card C := Nat.card_pos
    change L.relIndex C * Nat.card (L.subgroupOf C) = Nat.card C at hc
    intro hh
    rw [hh, zero_mul] at hc
    omega
  have hidx2 : L.relIndex C = 2 := by omega
  have hCcard : Nat.card C = 256 := by
    have hc := (L.subgroupOf C).index_mul_card
    have hsub : Nat.card (L.subgroupOf C) = 128 := by
      rw [← card_map_of_injective (K := L.subgroupOf C) C.subtype_injective,
        subgroupOf_map_subtype, hLC, hBcard]
    change L.relIndex C * Nat.card (L.subgroupOf C) = Nat.card C at hc
    rw [hidx2, hsub] at hc
    omega
  have hgen : C = B ⊔ zpowers y := by
    have hle : B ⊔ zpowers y ≤ C := sup_le hBC (zpowers_le.mpr hyC)
    have hBN : y ∈ normalizer (B : Set G) := by
      have hnormal : (B.subgroupOf C).Normal := by
        apply normal_of_index_eq_two
        change B.relIndex C = 2
        rw [← hLC, inf_relIndex_right]
        exact hidx2
      have hh := le_normalizer_map (H := B.subgroupOf C) C.subtype
      rw [normalizer_eq_top, ← MonoidHom.range_eq_map, C.range_subtype,
        map_subgroupOf_eq_of_le hBC] at hh
      exact hh hyC
    have hjcard : Nat.card (B ⊔ zpowers y : Subgroup G) = 256 := by
      rw [card_sup_zpowers_of_normalizing_involution B y (hy2 ▸ pow_orderOf_eq_one y)
        (fun hh => hyJ hh.1) hBN, hBcard]
    exact (eq_of_le_of_card_ge hle (by rw [hCcard, hjcard])).symm
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEL : E ≤ L := by
    rintro e ⟨eJ, _, rfl⟩
    exact mem_map_of_mem H.subtype eJ.property
  have hEB : E ≤ B := le_inf hEL ((le_centralizer E).trans (centralizer_le inf_le_left))
  have hVC : V ≤ C := inf_le_left.trans (hEB.trans hBC)
  have hcenterC : (center C).map C.subtype = V := by
    apply le_antisymm
    · rintro c ⟨cC, hcZ, rfl⟩
      have hcE : (cC : G) ∈ E := by
        rw [← show centralizer (E : Set G) = E from parrott_derived_centralizer z h]
        intro e he
        exact congrArg C.subtype (mem_center_iff.mp hcZ ⟨e, hBC (hEB he)⟩)
      exact ⟨hcE, mem_centralizer_singleton_iff.mpr
        (congrArg C.subtype (mem_center_iff.mp hcZ ⟨y, hyC⟩)).symm⟩
    · intro v hv
      refine ⟨⟨v, hVC hv⟩, mem_center_iff.mpr ?_, rfl⟩
      intro c
      exact Subtype.ext (c.property.2 v hv).symm
  exact ⟨hVcard, hBcard, hBM, hCcard, hgen, hcenterC⟩


end Stellmacher.Recognition.ParrottSecondElementaryData
