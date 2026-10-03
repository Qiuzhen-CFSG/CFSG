module

public import Stellmacher.Recognition.NormalEightQuaternionAbelianSetup
public import Theory.GroupTheory.QuaternionFixedEightNormal
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The elementary fixed-core branch for a four-group quotient

A fixed elementary eight in the quaternion core is normal in the whole Sylow
subgroup: the quaternion calculation identifies it with the relative
commutator, and the abelian quotient preserves that commutator. Thus the
normal-only elementary rank bound excludes a fixed eight. The extraspecial
order-32 bound then bounds an elementary fixed core by four.

The remaining branch requires the identification with the distinguished normal
four, the involution fusion calculation, and the final elementary centralizer
of order sixteen. These are not consequences of the normal-only rank bound
alone.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (b)(ii), printed p.391.
-/

open Subgroup
open Stellmacher.Recognition.NormalFourCentralOmegaTwo
namespace Stellmacher.Recognition.NormalEightNonnormalImage
variable {G : Type*} [Group G] [Finite G]

/-- A fixed elementary eight in the core preimage is normal in the entire Sylow
subgroup when the core quotient is abelian. -/
public theorem omegaCorePreimage_elementary_fixed_eight_normal
    (S : Sylow 2 G)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    [IsMulCommutative (S ⧸ omegaCorePreimage S)]
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : S) (ht : t ^ 2 = 1)
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))))
    (hcard : Nat.card ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))) = 8) :
    (omegaCorePreimage S ⊓ centralizer ({t} : Set S) : Subgroup S).Normal := by
  let H := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  let : IsExtraspecial 2 H := IsExtraspecial.of_mulEquiv e.symm inferInstance
  let B' := B.map e.symm.toMonoidHom
  let C' := C.map e.symm.toMonoidHom
  have hB' : Nonempty (B' ≃* QuaternionGroup 2) := by
    obtain ⟨f⟩ := hB
    exact ⟨(B.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans f⟩
  have hC' : Nonempty (C' ≃* QuaternionGroup 2) := by
    obtain ⟨f⟩ := hC
    exact ⟨(C.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans f⟩
  have hjoin' : B' ⊔ C' = ⊤ := by
    rw [← Subgroup.map_sup, hjoin, map_top_of_surjective _ e.symm.surjective]
  have hinter' : Nat.card (B' ⊓ C' : Subgroup H) = 2 := by
    rw [← map_inf B C e.symm.toMonoidHom e.symm.injective,
      card_map_of_injective e.symm.injective]
    exact hinter
  have hcomm' : ∀ b ∈ B', ∀ c ∈ C', b*c=c*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    simpa only [map_mul] using congrArg e.symm.toMonoidHom (hcomm b hb c hc)
  let E := centralizer ({t} : Set S)
  let F := H.subgroupOf E
  let : IsElementaryAbelian 2 F := hfixed
  have hmap : F.map E.subtype = H ⊓ E := subgroupOf_map_subtype H E
  have hfe : IsElementaryAbelian 2 (H ⊓ E : Subgroup S) := by
    rw [← hmap]
    exact IsElementaryAbelian.map E.subtype
  have hfc : Nat.card (H ⊓ E : Subgroup S) = 8 := by
    rw [← hmap, card_map_of_injective E.subtype_injective]
    exact hcard
  exact quaternion_fixed_eight_normal H ((card_omegaCorePreimage S).trans hH)
    B' C' hB' hC' hjoin' hinter' hcomm' t ht hfe hfc

/-- The normal-only rank bound excludes the fixed elementary eight. -/
public theorem omegaCorePreimage_elementary_fixed_card_ne_eight
    (S : Sylow 2 G)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    [IsMulCommutative (S ⧸ omegaCorePreimage S)]
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : S) (ht : t ^ 2 = 1)
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S)))) :
    Nat.card ((omegaCorePreimage S).subgroupOf (centralizer ({t} : Set S))) ≠ 8 := by
  intro hcard
  have hn := omegaCorePreimage_elementary_fixed_eight_normal
    S hH B C hB hC hjoin hinter hcomm t ht hfixed hcard
  let E := centralizer ({t} : Set S)
  let F := (omegaCorePreimage S).subgroupOf E
  let : IsElementaryAbelian 2 F := hfixed
  have hm : F.map E.subtype = omegaCorePreimage S ⊓ E := subgroupOf_map_subtype _ _
  apply hno ⟨F.map E.subtype, hm ▸ hn, IsElementaryAbelian.map E.subtype, ?_⟩
  rw [card_map_of_injective E.subtype_injective]
  exact hcard.ge

/-- Every elementary fixed core has order at most four; no bound on arbitrary
nonnormal elementary subgroups of the Sylow group is used. -/
public theorem omegaCorePreimage_elementary_fixed_card_le_four
    (S : Sylow 2 G)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    [IsMulCommutative (S ⧸ omegaCorePreimage S)]
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : S) (ht : t ^ 2 = 1)
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S)))) :
    Nat.card ((omegaCorePreimage S).subgroupOf (centralizer ({t} : Set S))) ≤ 4 := by
  let H := omegaCorePreimage S
  let E := centralizer ({t} : Set S)
  let F := H.subgroupOf E
  let : IsElementaryAbelian 2 F := hfixed
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let D := F.map E.subtype
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map E.subtype
  have hDH : D ≤ H := by
    rw [show D = H ⊓ E from subgroupOf_map_subtype H E]
    exact inf_le_left
  let : IsElementaryAbelian 2 (D.subgroupOf H) := IsElementaryAbelian.subgroupOf hDH
  have hcard : Nat.card (D.subgroupOf H) = Nat.card F :=
    (Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv).trans
      (card_map_of_injective E.subtype_injective)
  have hbound := IsExtraspecial.elementary_card_le_eight_of_card_thirty_two
    ((card_omegaCorePreimage S).trans hH) (D.subgroupOf H)
  rw [hcard] at hbound
  have hne := omegaCorePreimage_elementary_fixed_card_ne_eight
    S hno hH B C hB hC hjoin hinter hcomm t ht hfixed
  have hlt : Nat.card F < 8 := lt_of_le_of_ne hbound hne
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 F).exists_card_eq
  have hnlt : n < 3 := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) h
    rw [← hn] at hh
    norm_num at hh
    omega
  change Nat.card F ≤ 4
  interval_cases n <;> norm_num only [pow_zero, pow_one, Nat.reducePow] at hn <;> omega

omit [Finite G] in
/-- The fixed-core bound and core index bound the whole involution centralizer.
Equality forces both the fixed four and surjectivity onto the core quotient. -/
public theorem quaternion_four_centralizer_card_and_cover
    (S : Sylow 2 G) (t : S)
    (hindex : (omegaCorePreimage S).index = 4)
    (hfixed : Nat.card ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))) ≤ 4) :
    Nat.card (centralizer ({t} : Set S)) ≤ 16 ∧
      (Nat.card (centralizer ({t} : Set S)) = 16 →
        Nat.card ((omegaCorePreimage S).subgroupOf
          (centralizer ({t} : Set S))) = 4 ∧
        omegaCorePreimage S ⊔ centralizer ({t} : Set S) = ⊤) := by
  let H := omegaCorePreimage S
  let E := centralizer ({t} : Set S)
  have hdiv := relIndex_dvd_index_of_normal H E
  have hrel : H.relIndex E ≤ 4 := Nat.le_of_dvd (by decide)
    (hindex ▸ hdiv)
  have hmul := (H.subgroupOf E).card_mul_index
  change Nat.card (H.subgroupOf E) * H.relIndex E = Nat.card E at hmul
  have hbound : Nat.card E ≤ 16 := calc
    Nat.card E = Nat.card (H.subgroupOf E) * H.relIndex E := hmul.symm
    _ ≤ 4 * 4 := Nat.mul_le_mul hfixed hrel
    _ = 16 := rfl
  refine ⟨hbound, ?_⟩
  intro hE
  change Nat.card E = 16 at hE
  have hF : Nat.card (H.subgroupOf E) = 4 := by
    nlinarith [Nat.mul_le_mul_left (Nat.card (H.subgroupOf E)) hrel]
  have hrelEq : H.relIndex E = 4 := by
    rw [hF, hE] at hmul
    omega
  refine ⟨hF, index_eq_one.mp ?_⟩
  have hidx := relIndex_mul_index (show H ≤ H ⊔ E from le_sup_left)
  rw [relIndex_sup_left, hrelEq] at hidx
  change 4 * (H ⊔ E).index = H.index at hidx
  change H.index = 4 at hindex
  rw [hindex] at hidx
  change (H ⊔ E).index = 1
  omega

end Stellmacher.Recognition.NormalEightNonnormalImage
