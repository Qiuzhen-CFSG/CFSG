module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# The four-element common Sylow subgroup

The local two-cores have order two and are central, so neither vertex has
characteristic two. The proved exceptional-pair recognition therefore
identifies the actual amalgam with (D₁₂,E₄,D₁₂), including its embeddings.
The elementary Sylow and vertex models are extracted for F.6.18(4).

Source: Aschbacher–Smith F.6.5(ii), F.6.18(4), printed pp.305 and 310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
private theorem local_core_card_two (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) : Nat.card (pCore 2 G₁) = 2 := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let K := Q.subgroupOf (G₁ ⊓ G₂)
  have hi : K.index = 2 := h.left_core_index
  have hc := K.index_mul_card
  rw [hi, hT] at hc
  have hK : Nat.card K = 2 := by omega
  rw [Nat.card_congr ((pCore 2 G₁).equivMapOfInjective G₁.subtype
    G₁.subtype_injective).toEquiv]
  rw [← Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
  exact hK

theorem not_characteristic_two_of_intersection_four
    (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) :
    generalizedFitting G₁ ≠ pCore 2 G₁ := by
  intro he
  have hc := central_of_normal_card_two (pCore 2 G₁) (local_core_card_two h hT)
  have htotal : (⊤ : Subgroup G₁) ≤ centralizer (pCore 2 G₁ : Set G₁) := by
    intro x _
    apply mem_centralizer_iff.mpr
    intro y hy
    exact (mem_center_iff.mp (hc hy) x).symm
  have hself := centralizer_generalizedFitting_le G₁
  rw [he] at hself
  have ht : pCore 2 G₁ = ⊤ := top_unique (htotal.trans hself)
  have hi := SymmetricThreeTwoCore.core_index h.quotient_left.some
  rw [ht, index_top] at hi
  norm_num at hi

theorem four_intersection_amalgam
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      RankTwoAmalgam.dihedralTwelvePair) := by
  exact h.case_two_of_intersection_card_four hcore
    (not_characteristic_two_of_intersection_four h hT)
    (not_characteristic_two_of_intersection_four h.symm (by simpa only [inf_comm] using hT)) hT


theorem four_intersection_models
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) :
    IsElementaryAbelian 2 (G₁ ⊓ G₂ : Subgroup G) ∧
      Nonempty (G₁ ≃* DihedralGroup 6) ∧ Nonempty (G₂ ≃* DihedralGroup 6) := by
  obtain ⟨a⟩ := four_intersection_amalgam h hcore hT
  let : IsKleinFour (RankTwoAmalgam.swapMiddle × RankTwoAmalgam.swapMiddle) :=
    RankTwoAmalgam.dihedralTwelvePair_middle_isKleinFour
  let : IsElementaryAbelian 2 (RankTwoAmalgam.swapMiddle × RankTwoAmalgam.swapMiddle) :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  exact ⟨IsElementaryAbelian.of_surjective a.middle.symm.toMonoidHom a.middle.symm.surjective,
    ⟨a.left.trans RankTwoAmalgam.dihedralTwelveVertexEquiv⟩,
    ⟨a.right.trans RankTwoAmalgam.dihedralTwelveVertexEquiv⟩⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
