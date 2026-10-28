module
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Promotion
/-!
# The source five-normalizer product

The original odd core has center B₅ and hence the same normalizer as B₅.
The source order makes it an extraspecial Sylow five-group. The actual
normalizer splits over it with an order32 subgroup of H containing C_Q(B₅).

Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

/-- The distinguished five-subgroup is exactly the ambient image of Z(P). -/
theorem five_oddPart_center (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    (center (fiveOddPart B5)).map (fiveOddPart B5).subtype=B5Image B5 := by
  let : IsExtraspecial 5 (fiveOddPart B5) := five_oddPart_extraspecial c B5 hG
  have hBP := B5Image_le_fiveOddPart d.card_Z B5
  have hBc : (B5Image B5).subgroupOf (fiveOddPart B5)≤center (fiveOddPart B5) := by
    intro b hb
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext ((fiveOddPart_le_G5 B5 p.property) b hb).symm
  have he : (B5Image B5).subgroupOf (fiveOddPart B5)=center (fiveOddPart B5) :=
    eq_of_le_of_card_ge hBc (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv,
        B5Image_card d.card_Z B5,IsExtraspecial.center_order_p 5 (fiveOddPart B5)])
  rw [← he,map_subgroupOf_eq_of_le hBP]

/-- Characteristic-center preservation identifies the two actual normalizers. -/
theorem five_oddPart_normalizer (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    normalizer (fiveOddPart B5 : Set G)=normalizer (B5Image B5 : Set G) := by
  apply le_antisymm _ (normalizer_B5Image_le_normalizer_fiveOddPart B5)
  have hh := normalizer_le_normalizer_characteristic_image (fiveOddPart B5) (center (fiveOddPart B5))
  rwa [five_oddPart_center c B5 hG] at hh

/-- The same original P is an ambient Sylow five-group with the proved extraspecial structure. -/
theorem five_oddPart_sylow (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    ∃ S : Sylow 5 G, (S : Subgroup G)=fiveOddPart B5 ∧
      Nat.card S=125 ∧ IsExtraspecial 5 S := by
  obtain ⟨S,hS⟩ := exists_sylow_five_of_order hG (fiveOddPart B5)
    (SourceCompletion.five_oddPart_card c B5)
  refine ⟨S,hS,?_,?_⟩
  · rw [hS]
    exact SourceCompletion.five_oddPart_card c B5
  · rw [hS]
    exact five_oddPart_extraspecial c B5 hG

/-- The actual normalizer splits over P with an order32 subgroup of H;
the original z lies in that complement's center. -/
theorem exists_five_normalizer_product (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    ∃ R : Subgroup G, R≤d.toTypeRuSetup.H ∧ R≤normalizer (B5Image B5 : Set G) ∧
      Nat.card R=32 ∧ CQ B5≤R ∧ Disjoint (fiveOddPart B5) R ∧
      normalizer (B5Image B5 : Set G)=fiveOddPart B5 ⊔ R ∧
      c.z∈(center R).map R.subtype := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  obtain ⟨R,hR,hRc,hQR,_⟩ := exists_five_local_two c B5
  have hn : R≤normalizer (fiveOddPart B5 : Set G) :=
    (hR.trans inf_le_right).trans (normalizer_B5Image_le_normalizer_fiveOddPart B5)
  have hP := SourceCompletion.five_oddPart_card c B5
  have hd : Disjoint (fiveOddPart B5) R := disjoint_of_coprime_natCard (by rw [hP,hRc]; decide)
  have he : fiveOddPart B5 ⊔ R=normalizer (B5Image B5 : Set G) :=
    eq_of_le_of_card_ge (sup_le ((fiveOddPart_le_G5 B5).trans
      (Subgroup.centralizer_le_normalizer _)) (hR.trans inf_le_right)) (by
        rw [five_normalizer_card c B5,
          card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,hP,hRc])
  have hzR : c.z∈R := hQR (q.inf_U.symm ▸ c.z_mem_Z).1
  have hzc : (⟨c.z,hzR⟩ : R)∈center R := by
    apply mem_center_iff.mpr
    intro r
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ (hR r.property).1))
  exact ⟨R,hR.trans inf_le_left,hR.trans inf_le_right,hRc,hQR,hd,he.symm,⟨⟨c.z,hzR⟩,hzc,rfl⟩⟩

end CFSG.Quasithin.ChapterJ.Section03
