module

public import Stellmacher.Recognition.NormalEightNonnormalCyclicWeakClosure
public import Theory.GroupTheory.PGroup.CyclicCenterIndexFourElementary
public import Theory.GroupTheory.PGroup.ExtraspecialCyclicQuaternion
public import Theory.GroupTheory.PGroup.QuaternionCyclicEightNormalizer

/-!
# Elementary-eight normalizers in the large cyclic-tail branch

The core has cyclic center of index four and is nonabelian. Consequently
its elementary subgroups have order at most four. Every elementary eight
in the Sylow group crosses the index-two core and meets it in order four;
its Sylow normalizer has twice the order of its intersection with the core.
A characteristic quaternion-eight supplement to the cyclic center transports
from the quotient core to the actual core. Both factors are normal in the
Sylow group. The intrinsic quaternion and outside-action calculation gives
order sixteen for the intersection normalizer, hence order thirty-two for
the Sylow normalizer.

The calculation uses only the absence of normal elementary eights in the
Sylow group, not a bound on all of its elementary subgroups.

Source: Janko–Thompson (1970), §4, Case 2, printed p.393.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-- The cyclic center of the actual core has index four. -/
public theorem omegaCorePreimage_center_index_four_of_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ U : Subgroup S, U.Normal → IsElementaryAbelian 2 U →
      Nat.card U = 4 → U = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D) :
    (center (omegaCorePreimage S)).index = 4 := by
  have hD : D ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hlarge
    omega
  obtain ⟨_, hcenter⟩ := omegaCorePreimage_center_cyclic_tail
    S hno W hunique hnormal B D hD hc hgen
  have hS := card_sylow_eq_eight_mul_cyclic_tail
    hN S hZ W hW hno hunique hnormal B D hB hD hc hgen
  have hR := (omegaCorePreimage S).card_mul_index
  rw [omegaCorePreimage_index_two_of_cyclic_tail
    hN S hZ W hW hunique hnormal B D hB hgen, hS] at hR
  have hcount := (center (omegaCorePreimage S)).card_mul_index
  rw [hcenter] at hcount
  have hpos : 0 < Nat.card D := Nat.card_pos
  nlinarith

/-- The core, unlike the whole Sylow group, has elementary rank at most two. -/
public theorem omegaCorePreimage_elementary_card_le_four_of_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ U : Subgroup S, U.Normal → IsElementaryAbelian 2 U →
      Nat.card U = 4 → U = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D)
    (U : Subgroup (omegaCorePreimage S)) [IsElementaryAbelian 2 U] :
    Nat.card U ≤ 4 := by
  have hD : D ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hlarge
    omega
  let : IsCyclic (center (omegaCorePreimage S)) :=
    (omegaCorePreimage_center_cyclic_tail S hno W hunique hnormal B D hD hc hgen).1
  have hn : ¬ IsMulCommutative (omegaCorePreimage S) := by
    intro hcomm
    let : IsMulCommutative (omegaCorePreimage S) := hcomm
    apply omegaQuotient_pCore_noncommutative hN S hZ W hW hno hunique hnormal
    apply isMulCommutative_iff.mpr
    intro x y
    apply (omegaCorePreimageEquiv S).symm.injective
    rw [map_mul, map_mul, mul_comm]
  exact card_elementary_le_four_of_cyclic_center_index_four hn
    (omegaCorePreimage_center_index_four_of_cyclic_tail
      hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge) U

/-- Every elementary eight meets the core in four and its normalizer crosses
the core. The order-thirty-two conclusion reduces to an intersection of order sixteen. -/
public theorem elementary_eight_normalizer_core_reduction_of_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ U : Subgroup S, U.Normal → IsElementaryAbelian 2 U →
      Nat.card U = 4 → U = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D)
    (F : Subgroup S) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8) :
    ¬ F ≤ omegaCorePreimage S ∧
      Nat.card ((omegaCorePreimage S).subgroupOf F) = 4 ∧
      Nat.card (normalizer (F : Set S)) =
        2 * Nat.card ((omegaCorePreimage S).subgroupOf (normalizer (F : Set S))) := by
  have hout : ¬ F ≤ omegaCorePreimage S := by
    intro hle
    let : IsElementaryAbelian 2 (F.subgroupOf (omegaCorePreimage S)) :=
      IsElementaryAbelian.subgroupOf hle
    have hb := omegaCorePreimage_elementary_card_le_four_of_cyclic_tail
      hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge
      (F.subgroupOf (omegaCorePreimage S))
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hF] at hb
    omega
  have hi := omegaCorePreimage_index_two_of_cyclic_tail
    hN S hZ W hW hunique hnormal B D hB hgen
  exact ⟨hout, card_intersection_four_of_elementary_eight_not_le _ _ hi hF hout,
    card_normalizer_eq_two_mul_core_intersection _ _ hi hout⟩

/-- Every elementary eight has Sylow normalizer of order thirty-two in the
large cyclic-tail branch. The normal-only rank hypothesis suffices. -/
public theorem card_elementary_eight_normalizer_eq_thirty_two_of_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ U : Subgroup S, U.Normal → IsElementaryAbelian 2 U →
      Nat.card U = 4 → U = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D) :
    ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      Nat.card (normalizer (F : Set S)) = 32 := by
  let H := pCore 2 (OmegaQuotient S)
  let R := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  let : IsCyclic (center H) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  have hD : D ≠ ⊥ := by intro h; simp [h] at hlarge
  have hHD : center H = D :=
    center_eq_cyclic_factor_of_extraspecial_of_cyclic_center
      pCore_isPGroup B D hD hc hgen
  obtain ⟨Q₀, _, ⟨e₀⟩, hQ₀⟩ :=
    exists_characteristic_quaternion_of_extraspecial_cyclic_product
      pCore_isPGroup B D hB hlarge hc hgen
  let Q₁ := Q₀.map e.symm.toMonoidHom
  let e₁ : Q₁ ≃* QuaternionGroup 2 :=
    (Q₀.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans e₀
  have hDmap : D.map e.symm.toMonoidHom ≤ center R := by
    rintro x ⟨d, hd, rfl⟩
    apply mem_center_iff.mpr
    intro r
    simpa using congrArg e.symm
      (mem_center_iff.mp (show d ∈ center H from hHD.symm ▸ hd) (e r))
  have hQ₁ : Q₁ ⊔ center R = ⊤ := by
    apply top_unique
    calc
      ⊤ = (Q₀ ⊔ D).map e.symm.toMonoidHom := by
        rw [hQ₀, map_top_of_surjective _ e.symm.surjective]
      _ = Q₁ ⊔ D.map e.symm.toMonoidHom := map_sup _ _ _
      _ ≤ Q₁ ⊔ center R := sup_le_sup_left hDmap _
  obtain ⟨hRc, hRcard⟩ := omegaCorePreimage_center_cyclic_tail
    S hno W hunique hnormal B D hD hc hgen
  let : IsCyclic (center R) := hRc
  let : Q₁.Characteristic := quaternion_supplement_characteristic Q₁ e₁ hQ₁
  have hRi : R.index = 2 := omegaCorePreimage_index_two_of_cyclic_tail
    hN S hZ W hW hunique hnormal B D hB hgen
  let : R.Normal := normal_of_index_eq_two hRi
  let Q := Q₁.map R.subtype
  let C := (center R).map R.subtype
  let : Q.Normal := ConjAct.normal_of_characteristic_of_normal
  let : C.Normal := ConjAct.normal_of_characteristic_of_normal
  let eQ : Q ≃* QuaternionGroup 2 :=
    (Q₁.equivMapOfInjective R.subtype R.subtype_injective).symm.trans e₁
  let eC := (center R).equivMapOfInjective R.subtype R.subtype_injective
  let : IsCyclic C := eC.isCyclic.mp inferInstance
  have hCcard : Nat.card C = Nat.card D :=
    (card_map_of_injective R.subtype_injective).trans hRcard
  have hQC : C ≤ centralizer (Q : Set S) := by
    rintro c ⟨z, hz, rfl⟩ q ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz u)
  have hQgen : Q ⊔ C = R := by
    change Q₁.map R.subtype ⊔ (center R).map R.subtype = R
    rw [← Subgroup.map_sup, hQ₁]
    ext x
    constructor
    · rintro ⟨r, _, rfl⟩
      exact r.property
    · intro hx
      exact ⟨⟨x, hx⟩, mem_top _, rfl⟩
  have hQcard : Nat.card Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hinter : Nat.card (Q ⊓ C : Subgroup S) = 2 := by
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q C
      (hQC.trans (Subgroup.centralizer_le_normalizer _))
    rw [hQcard, hCcard, hQgen] at hprod
    have hindex := (center R).card_mul_index
    rw [omegaCorePreimage_center_index_four_of_cyclic_tail
      hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge,
      hRcard] at hindex
    have hpos : 0 < Nat.card D := Nat.card_pos
    nlinarith
  intro F hFe hF
  let : IsElementaryAbelian 2 F := hFe
  obtain ⟨hout, hcap, hdouble⟩ := elementary_eight_normalizer_core_reduction_of_cyclic_tail
    hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge F hF
  have hcount := card_core_normalizer_eq_sixteen_of_quaternion_cyclic_core
    S.isPGroup' R Q C W hRi inferInstance inferInstance ⟨eQ⟩ inferInstance
    (by rwa [hCcard]) hQC hQgen hinter rfl inferInstance inferInstance hW hunique
    F hFe hF hout hcap
  rw [hcount] at hdouble
  exact hdouble

end Stellmacher.Recognition.NormalEightNonnormalImage
