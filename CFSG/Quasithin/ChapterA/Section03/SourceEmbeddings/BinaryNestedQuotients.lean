module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import Theory.GroupTheory.CComponent.LocalQuotientOrder
public import CFSG.Quasithin.ClassicalModels

/-!
# Strict local-component chains in a binary five-space quotient

The intrinsic Levi calculation gives degrees three, four and five for
local components in GL₅(2). A strict enlargement of a local PSL₃(2)
section cannot have degree three: equality of the quotient orders forces
equality of the original local components. Thus only degrees four and
five remain. The proof keeps the original inclusion and the full Sylow
intersections through the actual containing-component quotient.

Source: Aschbacher--Smith, the PSL₅(2) comparison in 12.9.3,
printed pp.858--859. Its source application is Components/Binary.lean.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryNested
open BinaryLinear.OuterCyclic BinaryIntrinsic
variable {G : Type*} [Group G] [Finite G]

private noncomputable def binaryEquiv {X : Type*} [Group X]
    {d : ℕ} (hd : 0 < d) (hm : ClassicalGroup.IsPSL X d 2) : X ≃* LinearGroup d := Classical.choice <| by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := hm
  let := Fintype.ofFinite k
  let f : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
  exact ⟨(e.trans (Atlas.fieldEquivPSL d f)).trans (projectiveEquivLinear hd)⟩

/-- Comparable original local C-components are equal if their intrinsic
two-core quotient orders do not increase. -/
theorem local_eq_of_twoCore_card_le
    (T : Sylow 2 G) {B D : Subgroup G}
    (hB : B ∈ localCComponents T)
    (hD : D ∈ localCComponents T) (hBD : B ≤ D)
    (hc : Nat.card (D ⧸ pCore 2 D) ≤ Nat.card (B ⧸ pCore 2 B)) : B = D := by
  obtain ⟨S,_,hBS⟩ := local_in_local_overgroup T hB hD hBD
  let eD := subgroupOfEquivOfLe (show D ≤ D ⊔ (T : Subgroup G) from le_sup_left)
  have ht : (⊤ : Subgroup (D.subgroupOf (D ⊔ (T : Subgroup G)))).IsCComponent := by
    simpa only [subgroupOf_self] using hD.subgroupOf le_rfl
  have htD : (⊤ : Subgroup D).IsCComponent := by
    simpa only [map_top_of_surjective eD.toMonoidHom eD.surjective] using ht.map_equiv eD
  let eB := subgroupOfEquivOfLe hBD
  have he := Subgroup.local_cComponent_eq_top_of_twoCore_card_le S (B.subgroupOf D) hBS htD (by
    rw [Nat.card_congr (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).toEquiv]
    exact hc)
  exact le_antisymm hBD (subgroupOf_eq_top.mp he)

/-- A strict containing local component in a binary five-space quotient
has degree four or five, whenever the smaller quotient is PSL₃(2). -/
theorem strict_three_in_five_models
    (T : Sylow 2 G) {B D J : Subgroup G}
    (hB : B ∈ localCComponents T)
    (hD : D ∈ localCComponents T)
    (hJ : J ∈ localCComponents T)
    (hBD : B < D) (hDJ : D ≤ J)
    (hBm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2)
    (hJm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 5 2) :
    ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 4 2 ∨
      ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 5 2 := by
  obtain ⟨d,hd,hd',⟨e⟩⟩ := local_twoCore_quotient_of_containing_quotient
    T hD hJ hDJ 5 (by decide) (binaryEquiv (by decide) hJm)
  have hm : ClassicalGroup.IsPSL (D ⧸ pCore 2 D) d 2 :=
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
      ⟨e.trans (projectiveEquivLinear (by omega)).symm⟩⟩
  have hne : d ≠ 3 := by
    intro he
    subst d
    have hcard : Nat.card (D ⧸ pCore 2 D) = Nat.card (B ⧸ pCore 2 B) :=
      Nat.card_congr (e.trans (binaryEquiv (by decide) hBm).symm).toEquiv
    exact hBD.ne (local_eq_of_twoCore_card_le T hB hD hBD.le hcard.le)
  rcases (show d = 4 ∨ d = 5 by omega) with rfl | rfl
  · exact Or.inl hm
  · exact Or.inr hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryNested
