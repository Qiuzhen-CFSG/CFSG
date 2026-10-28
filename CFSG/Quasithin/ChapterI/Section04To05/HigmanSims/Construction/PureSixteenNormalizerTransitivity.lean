module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PureSixteenIncidence
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExteriorTransitivity
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenIntersectionNonseed
public import Theory.ElementaryAbelian.Injective

/-!
# Full normalizer transitivity on the original pure sixteen

For any two nonidentity points, their point-core intersections are proper
subgroups of the same sixteen. Two proper subgroups cannot cover a group,
so there is a third point outside both intersections. Reciprocity places
the first two points outside that third point's intersection. Its original
point core normalizes the sixteen and is transitive on that exterior.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem normalizer_transitive (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 →
      ∃ g ∈ normalizer (A : Set G), g * x * g⁻¹ = y := by
  classical
  intro x hx hx1 y hy hy1
  let X := A ⊓ (involutionCentralizer x).pCoreIn 2
  let Y := A ⊓ (involutionCentralizer y).pCoreIn 2
  have hx8 : Nat.card X = 8 := hpoints x hx hx1
  have hy8 : Nat.card Y = 8 := hpoints y hy hy1
  have hn : ¬ (A : Set G) ⊆ (X : Set G) ∪ (Y : Set G) := by
    intro hh
    rcases SubgroupClass.subset_union.mp hh with hh | hh
    · have hc := card_le_of_le hh
      rw [hA, hx8] at hc
      omega
    · have hc := card_le_of_le hh
      rw [hA, hy8] at hc
      omega
  obtain ⟨r, hrA, hr⟩ := Set.not_subset.mp hn
  obtain ⟨hrX, hrY⟩ := not_or.mp hr
  have hr1 : r ≠ 1 := fun he => hrX (he ▸ X.one_mem)
  have hrz := hpure r hrA hr1
  obtain ⟨R, hrT⟩ := h.exists_typeAt_of_isConj r hrz
  have hrQ : r ∈ (involutionCentralizer r).pCoreIn 2 := by
    change r ∈ (pCore 2 (involutionCentralizer r)).map (involutionCentralizer r).subtype
    rw [← hrT.centralizer_fitting]
    exact hrT.seed_le_core hrT.involution_mem_seed
  let D := A ⊓ (involutionCentralizer r).pCoreIn 2
  have hDe : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.of_injective (inclusion (show D ≤ A from inf_le_left))
      (inclusion_injective _)
  let E : pointCoreEights r := ⟨D, inf_le_right, ⟨hrA, hrQ⟩, hDe, hpoints r hrA hr1⟩
  have hEn : E.val ∉ pointCoreSeedOrbit r R :=
    hrT.eight_in_sixteen_not_seed E A hA inf_le_left
  have hxE : x ∉ E.val := by
    intro hh
    exact hrX ⟨hrA, (h.conjugate_point_core_reciprocal x r (hpure x hx hx1) hrz).mpr hh.2⟩
  have hyE : y ∉ E.val := by
    intro hh
    exact hrY ⟨hrA, (h.conjugate_point_core_reciprocal y r (hpure y hy hy1) hrz).mpr hh.2⟩
  obtain ⟨g, hg, he⟩ :=
    hrT.nonseed_extension_exterior_transitive E hEn A hA inf_le_left x hx hxE y hy hyE
  have hQN := (hrT.nonseed_eight_extension_structure E hEn A inf_le_left inferInstance hA).1
  exact ⟨g, hQN hg, he⟩

/-- The actual sixteen supplied by the original local type has a full
normalizer transitive on all fifteen nonidentity elements. Every earlier
source marking and both literal extensions are retained. -/
theorem TypeAt.exists_normalizer_transitive_sixteen (h : TypeAt z V) :
    ∃ (u c b : G) (E : pointCoreEights u),
      u ∈ V ∧ u ≠ 1 ∧ TypeAt u V ∧ E.val ∉ pointCoreSeedOrbit u V ∧
      Nat.card (centralizer (E.val : Set G)) = 32 ∧
      Nat.card (involutionCentralizer u ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 ∧
      orderOf c = 4 ∧ c ^ 2 = u ∧
      c ∈ (center ((involutionCentralizer u).pCoreIn 2)).map
        ((involutionCentralizer u).pCoreIn 2).subtype ∧
      b ^ 2 = 1 ∧ IsConj b z ∧ ¬ Commute b c ∧ b * c * b⁻¹ = c⁻¹ ∧
      (center (centralizer (E.val : Set G))).map
        (centralizer (E.val : Set G)).subtype = E.val ∧
      let A := E.val ⊔ zpowers b
      let B := E.val ⊔ zpowers (c * b)
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ A ≠ B ∧ A ⊓ B = E.val ∧
      (involutionCentralizer u).pCoreIn 2 ≤ normalizer (A : Set G) ⊓ normalizer (B : Set G) ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ (involutionCentralizer u).pCoreIn 2 = E.val ∧
      B ⊓ (involutionCentralizer u).pCoreIn 2 = E.val ∧
      (∀ x ∈ A, x ∉ E.val → ∃ q ∈ (involutionCentralizer u).pCoreIn 2, q * b * q⁻¹ = x) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ E.val, x ≠ 1 → x ≠ u → ∀ y ∈ E.val, y ≠ 1 → y ≠ u →
        ∃ g ∈ (involutionCentralizer u ⊓ normalizer (E.val : Set G)) ⊓ normalizer (A : Set G),
          g * x * g⁻¹ = y) ∧
      (∀ x ∈ A, x ≠ 1 →
        Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 →
        ∃ g ∈ normalizer (A : Set G), g * x * g⁻¹ = y) ∧
      (∀ F : Subgroup G,
        (E.val ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  obtain ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768, hc4, hc2, hcZ,
    hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN,
    hCA, hCB, hAQ, hBQ, horbit, hpure, hinner, hpoints, hall⟩ :=
    h.exists_all_point_core_eights
  let := hAe
  have htrans := normalizer_transitive h _ hA16 hpure hpoints
  exact ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768, hc4, hc2, hcZ,
    hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN,
    hCA, hCB, hAQ, hBQ, horbit, hpure, hinner, hpoints, htrans, hall⟩

end CFSG.Quasithin.HigmanSims
