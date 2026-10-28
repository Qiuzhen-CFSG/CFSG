module

public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicTransferSetup
public import Theory.GroupTheory.PGroup.LargeHallInvolutionCentralizer
public import Theory.GroupTheory.PGroup.LargeHallInternalInvolutionCentralizer
public import Theory.GroupTheory.CentralizerEmbeddingTransport

/-!
# Outside-rotation centralizers in the actual Sylow subgroup

The internal Hall-factor calculation supplies an extraspecial subgroup of order
eight in the involution centralizer and bounds the core centralizer by sixteen.
Transport these facts from the quotient core to the actual core. The index-two
extension theorem identifies the central derived line, and the index bound gives
order at most thirty-two. Finally an injective embedding transports the line to
the actual ambient image in `G`.

The final assembly discharges the internal calculation using the extraspecial
factor of order eight. It imposes no special choice or full-centralization
hypothesis on the outside-rotation involution.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, printed pp.392–393.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

private theorem map_fourth_power_closure
    {P T : Type*} [Group P] [Group T] (e : P ≃* T) :
    (closure {u : P | u ^ 4 ≠ 1}).map e.toMonoidHom =
      closure {u : T | u ^ 4 ≠ 1} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩ he
    change (e v) ^ 4 = 1 at he
    apply hv
    apply e.injective
    simpa only [map_pow, map_one] using he
  · intro hu
    refine ⟨e.symm u, ?_, e.apply_symm_apply u⟩
    intro he
    apply hu
    simpa only [map_pow, map_one, e.apply_symm_apply] using congrArg e he

private theorem map_centralizer_singleton_equiv
    {P T : Type*} [Group P] [Group T] (e : P ≃* T) (u : P) :
    (centralizer ({u} : Set P)).map e.toMonoidHom =
      centralizer ({e u} : Set T) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e w * e u = e u * e w
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hw)
  · intro hv
    refine ⟨e.symm v, mem_centralizer_singleton_iff.mpr ?_, e.apply_symm_apply v⟩
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hv

private theorem card_centralizer_le_thirty_two_of_core_bound
    {T : Type*} [Group T] [Finite T]
    (H : Subgroup T) [H.Normal] (hi : H.index = 2) (u : H)
    (hcard : Nat.card (centralizer ({u} : Set H)) ≤ 16) :
    Nat.card (centralizer ({(u : T)} : Set T)) ≤ 32 := by
  let C := centralizer ({(u : T)} : Set T)
  have he : (centralizer ({u} : Set H)).map H.subtype = H ⊓ C := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hw))⟩
    · rintro ⟨hv, hc⟩
      exact ⟨⟨v, hv⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)), rfl⟩
  have hc : Nat.card (H.subgroupOf C) ≤ 16 := by
    rw [← card_map_of_injective C.subtype_injective, subgroupOf_map_subtype,
      ← he, card_map_of_injective H.subtype_injective]
    exact hcard
  have hind : (H.subgroupOf C).index ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    rw [← hi]
    exact H.relIndex_dvd_index_of_normal C
  have hmul := (H.subgroupOf C).card_mul_index
  change Nat.card C ≤ 32
  nlinarith

variable {G : Type*} [Group G] [Finite G]

/-- Assembly of the actual ambient centralizer geometry from the internal
Hall-product calculation. The internal premise is uniform over all involutions
outside the intrinsic rotation subgroup. -/
public theorem outside_rotation_centralizer_geometry_of_internal_calculation
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2)
    (hcalc : ∀ y : pCore 2 (OmegaQuotient S), orderOf y = 2 →
      y ∉ closure {u : pCore 2 (OmegaQuotient S) | u ^ 4 ≠ 1} →
      IsExtraspecial 2 (closure {u : pCore 2 (OmegaQuotient S) | u ^ 4 ≠ 1} ⊓
        centralizer ({y} : Set (pCore 2 (OmegaQuotient S))) :
          Subgroup (pCore 2 (OmegaQuotient S))) ∧
      Nat.card (closure {u : pCore 2 (OmegaQuotient S) | u ^ 4 ≠ 1} ⊓
        centralizer ({y} : Set (pCore 2 (OmegaQuotient S))) :
          Subgroup (pCore 2 (OmegaQuotient S))) = 8 ∧
      Nat.card (centralizer ({y} : Set (pCore 2 (OmegaQuotient S)))) ≤ 16)
    (z : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (x : S) (hxH : x ∈ omegaCorePreimage S)
    (hxR : x ∉ (closure {u : omegaCorePreimage S | u ^ 4 ≠ 1}).map
      (omegaCorePreimage S).subtype) (hx : orderOf x = 2) :
    let Q := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
    (commutator Q ⊓ center Q).map Q.subtype = zpowers (z : G) ∧
      Nat.card (centralizer ({x} : Set S)) ≤ 32 := by
  let H := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  let : IsCyclic (center H) := (centerCongr e).isCyclic.mpr inferInstance
  have hzW : z ∈ W := by
    apply omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    refine ⟨⟨z, hzc⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z
  let zH : H := ⟨z, four_le_omegaCorePreimage hN S hZ W hW hno hzW⟩
  let xH : H := ⟨x, hxH⟩
  have hzHC : e zH ∈ center (pCore 2 (OmegaQuotient S)) := by
    exact (centerCongr e ⟨zH, mem_center_iff.mpr
      (fun u => Subtype.ext (mem_center_iff.mp hzc u))⟩).property
  have hzO : orderOf (e zH) = 2 := by
    rw [e.orderOf_eq, ← orderOf_coe]
    exact hz
  have hzrot := central_involution_mem_fourth_power_closure_of_large_hall
    pCore_isPGroup B D hD hn hc hg hlarge (e zH) hzHC hzO
  have hzR : zH ∈ closure {u : H | u ^ 4 ≠ 1} := by
    rw [← map_fourth_power_closure e] at hzrot
    obtain ⟨u, hu, he⟩ := hzrot
    exact e.injective he ▸ hu
  have hxR' : xH ∉ closure {u : H | u ^ 4 ≠ 1} :=
    fun h => hxR (mem_map_of_mem H.subtype h)
  have hyR : e xH ∉ closure {u : pCore 2 (OmegaQuotient S) | u ^ 4 ≠ 1} := by
    rw [← map_fourth_power_closure e]
    rintro ⟨u, hu, he⟩
    exact hxR' (e.injective he ▸ hu)
  have hxO : orderOf xH = 2 := (orderOf_coe xH).symm.trans hx
  obtain ⟨hextra, hcard, hcent⟩ := hcalc (e xH) (e.orderOf_eq xH |>.trans hxO) hyR
  let K := closure {u : H | u ^ 4 ≠ 1} ⊓ centralizer ({xH} : Set H)
  have hK : K.map e.toMonoidHom =
      closure {u : pCore 2 (OmegaQuotient S) | u ^ 4 ≠ 1} ⊓
        centralizer ({e xH} : Set (pCore 2 (OmegaQuotient S))) := by
    rw [map_inf _ _ _ e.injective, map_fourth_power_closure e,
      map_centralizer_singleton_equiv e xH]
  have hKextra : IsExtraspecial 2 K :=
    IsExtraspecial.of_mulEquiv (e.subgroupMap K).symm (hK.symm ▸ hextra)
  have hKcard : Nat.card K = 8 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hK]
    exact hcard
  have hCH : Nat.card (centralizer ({xH} : Set H)) ≤ 16 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective,
      map_centralizer_singleton_equiv e xH]
    exact hcent
  have hline := (involution_centralizer_line_of_intrinsic_extraspecial H hi
    xH zH hzc ((orderOf_coe zH).symm.trans hz) hxO hzR hxR'
      hKextra hKcard hCH).2
  exact ⟨derived_center_line_map_of_injective (centralizer ({x} : Set S))
    (S : Subgroup G).subtype Subtype.val_injective z hline,
    card_centralizer_le_thirty_two_of_core_bound H hi xH hCH⟩

/-- Every outside-rotation core involution has the central derived line generated
by the central involution; its centralizer in the Sylow subgroup has order at
most thirty-two. -/
public theorem outside_rotation_centralizer_geometry
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2)
    (z : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (x : S) (hxH : x ∈ omegaCorePreimage S)
    (hxR : x ∉ (closure {u : omegaCorePreimage S | u ^ 4 ≠ 1}).map
      (omegaCorePreimage S).subtype) (hx : orderOf x = 2) :
    let Q := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
    (commutator Q ⊓ center Q).map Q.subtype = zpowers (z : G) ∧
      Nat.card (centralizer ({x} : Set S)) ≤ 32 := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  apply outside_rotation_centralizer_geometry_of_internal_calculation
    hN S hno hZ W hW hunique hnormal B D hD hn hc hg hlarge hi
    ?_ z hzc hz x hxH hxR hx
  intro y hy hout
  obtain ⟨hextra, hcard, hcent⟩ := internal_involution_centralizer_of_large_hall
    pCore_isPGroup B D hB hD hn hc hg hlarge y hy hout
  exact ⟨hextra, hcard, hcent.le⟩

end Stellmacher.Recognition.NormalEightNonnormalImage
