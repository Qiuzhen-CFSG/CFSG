module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams
public import Theory.GroupTheory.SelfCentralizingNormalFourRecognition
public import Theory.GroupTheory.Amalgam.SylowRigidity
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# The characteristic-two vertex with Sylow subgroup of order eight

The core has index two in the actual common Sylow subgroup. Thus its order
is four and the vertex has order twenty-four. Fitting self-centralization
and the cubic action identify it with S₄. Sylow conjugacy then marks the
entire original overlap in a specified Sylow subgroup of the model.

Source: the mixed cases of Aschbacher–Smith F.6.5(2)(iii–iv), printed p.305.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The intrinsic characteristic-two vertex is self-centralizing on its core. -/
theorem IsGoldschmidtTriple.local_core_selfCentralizing
    (h : IsGoldschmidtTriple G₁ G₂) (hgood : generalizedFitting G₁ = pCore 2 G₁) :
    centralizer (pCore 2 G₁ : Set G₁) ≤ pCore 2 G₁ := by
  have hf : fittingSubgroup G₁ = pCore 2 G₁ :=
    (SymmetricThreeTwoCore.generalizedFitting_eq_fitting h.quotient_left.some).symm.trans hgood
  rw [← hf]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable h.local_solvable

/-- Recognition of the actual good vertex at common Sylow order eight. -/
theorem IsGoldschmidtTriple.local_equiv_symmetric_four_of_intersection_card_eight
    (h : IsGoldschmidtTriple G₁ G₂) (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8) :
    Nonempty (G₁ ≃* Equiv.Perm (Fin 4)) := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let K := Q.subgroupOf (G₁ ⊓ G₂)
  have hi : K.index = 2 := h.left_core_index
  have hc := K.index_mul_card
  rw [hi, hT] at hc
  have hK : Nat.card K = 4 := by omega
  have hQ : Nat.card (pCore 2 G₁) = 4 := by
    rw [Nat.card_congr ((pCore 2 G₁).equivMapOfInjective G₁.subtype
      G₁.subtype_injective).toEquiv]
    rw [← Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
    exact hK
  apply mulEquiv_perm_four_of_selfCentralizing_normal_four (pCore 2 G₁)
    pCore_isPGroup hQ (h.local_core_selfCentralizing hgood)
  rw [SymmetricThreeTwoCore.card_eq h.quotient_left.some, hQ]

/-- Recognition includes an exact marking of the original overlap in any
chosen Sylow subgroup of S₄. -/
theorem IsGoldschmidtTriple.local_marked_symmetric_four_of_intersection_card_eight
    (h : IsGoldschmidtTriple G₁ G₂) (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (S : Sylow 2 (Equiv.Perm (Fin 4))) :
    ∃ e : G₁ ≃* Equiv.Perm (Fin 4), ∃ u : (G₁ ⊓ G₂ : Subgroup G) ≃* S,
      ∀ t, e (inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left) t) = u t := by
  obtain ⟨e⟩ := h.local_equiv_symmetric_four_of_intersection_card_eight hgood hT
  obtain ⟨T, hTs⟩ := h.intersection_sylow
  have hTG : (T : Subgroup G) ≤ G₁ := hTs.symm.le.trans inf_le_left
  let P := T.subtype hTG
  have hp : (P : Subgroup G₁) = (inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left)).range := by
    ext x
    change (x : G) ∈ (T : Subgroup G) ↔ _
    rw [← hTs]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  exact exists_normalized_endpoint (inclusion inf_le_left) (S : Subgroup (Equiv.Perm (Fin 4))).subtype
    (inclusion_injective inf_le_left) (S : Subgroup (Equiv.Perm (Fin 4))).subtype_injective P hp S
    (by rw [range_subtype]) e

/-- The common group itself is dihedral of order eight in this branch. -/
theorem IsGoldschmidtTriple.intersection_equiv_dihedral_four_of_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8) :
    Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4) := by
  let S : Sylow 2 (Equiv.Perm (Fin 4)) := default
  obtain ⟨_, u, _⟩ := h.local_marked_symmetric_four_of_intersection_card_eight hgood hT S
  obtain ⟨v⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four S
  exact ⟨u.trans v⟩

/-- Mark the literal overlap image in `G/O₂(G)` inside any chosen Sylow of S₄.
Only the branch hypotheses (characteristic two and overlap order eight) remain. -/
theorem IsGoldschmidtTriple.quotient_marked_symmetric_four_of_intersection_card_eight
    (h : IsGoldschmidtTriple G₁ G₂)
    (hgood : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (hT : Nat.card ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G))) = 8)
    (S : Sylow 2 (Equiv.Perm (Fin 4))) :
    let q := QuotientGroup.mk' (pCore 2 G)
    ∃ e : G₁.map q ≃* Equiv.Perm (Fin 4),
      ∃ u : (G₁ ⊓ G₂).map q ≃* S,
        ∀ t, e (inclusion (Subgroup.map_mono inf_le_left) t) = u t := by
  have hT' : Nat.card (G₁.map (QuotientGroup.mk' (pCore 2 G)) ⊓
      G₂.map (QuotientGroup.mk' (pCore 2 G)) : Subgroup (G ⧸ pCore 2 G)) = 8 := by
    rw [← h.quotient_twoCore_intersection]
    exact hT
  obtain ⟨e, u, hu⟩ :=
    h.quotient_twoCore.local_marked_symmetric_four_of_intersection_card_eight hgood hT' S
  let v := MulEquiv.subgroupCongr h.quotient_twoCore_intersection
  exact ⟨e, v.trans u, fun t => hu (v t)⟩

end CFSG.Quasithin.ChapterF
