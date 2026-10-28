module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedInnerTransitivity
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointIncidenceCounts
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreConjugation
public import Theory.Combinatorics.SixEightIncidence

/-!
# Every point-core intersection of the original pure sixteen is an eight

The actual stabilizer is transitive on the six inner points. Their reciprocal
incidences with the eight exterior points satisfy the six-by-eight counting
identity. The resulting degrees identify all literal point-core intersections.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z u : G} {V : Subgroup G}

private theorem all_point_intersections_eight (h : TypeAt z V) (huT : TypeAt u V)
    (E : pointCoreEights u) (hEn : E.val ∉ pointCoreSeedOrbit u V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hEA : E.val ≤ A)
    (hAQ : A ⊓ (involutionCentralizer u).pCoreIn 2 = E.val)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hinner : ∀ x ∈ E.val, x ≠ 1 → x ≠ u → ∀ y ∈ E.val, y ≠ 1 → y ≠ u →
      ∃ g ∈ (involutionCentralizer u ⊓ normalizer (E.val : Set G)) ⊓ normalizer (A : Set G),
        g * x * g⁻¹ = y) :
    ∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8 := by
  classical
  let X := {x : G // x ∈ E.val ∧ x ∉ zpowers u}
  let Y := {y : G // y ∈ A ∧ y ∉ E.val}
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  let R (x : X) (y : Y) : Prop := (y : G) ∈ (involutionCentralizer (x : G)).pCoreIn 2
  have hX : Fintype.card X = 6 := by
    rw [← Nat.card_eq_fintype_card]
    change ((E.val : Set G) \ (zpowers u : Set G)).ncard = 6
    rw [Set.ncard_sdiff (show (zpowers u : Set G) ⊆ E.val from zpowers_le.mpr E.property.2.1)]
    change Nat.card E.val - Nat.card (zpowers u) = 6
    rw [E.property.2.2.2, Nat.card_zpowers, huT.involution]
  have hY : Fintype.card Y = 8 := by
    rw [← Nat.card_eq_fintype_card]
    change ((A : Set G) \ (E.val : Set G)).ncard = 8
    rw [Set.ncard_sdiff hEA]
    change Nat.card A - Nat.card E.val = 8
    rw [hA, E.property.2.2.2]
  have row_eq (x : X) : Fintype.card {y // R x y} =
      ({b : G | b ∈ A ∧ b ∉ E.val ∧ b ∈ (involutionCentralizer (x : G)).pCoreIn 2} : Set G).ncard := by
    let e : {y // R x y} ≃ {b : G // b ∈ A ∧ b ∉ E.val ∧
        b ∈ (involutionCentralizer (x : G)).pCoreIn 2} := {
      toFun y := ⟨y.val, y.val.property.1, y.val.property.2, y.property⟩
      invFun b := ⟨⟨b, b.property.1, b.property.2.1⟩, b.property.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact (Nat.card_eq_fintype_card.symm.trans (Nat.card_congr e))
  have col_eq (y : Y) : Fintype.card {x // R x y} =
      ({v : G | v ∈ E.val ∧ v ∉ zpowers u ∧ (y : G) ∈ (involutionCentralizer v).pCoreIn 2} : Set G).ncard := by
    let e : {x // R x y} ≃ {v : G // v ∈ E.val ∧ v ∉ zpowers u ∧
        (y : G) ∈ (involutionCentralizer v).pCoreIn 2} := {
      toFun x := ⟨x.val, x.val.property.1, x.val.property.2, x.property⟩
      invFun v := ⟨⟨v, v.property.1, v.property.2.1⟩, v.property.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact (Nat.card_eq_fintype_card.symm.trans (Nat.card_congr e))
  have hrow (x : X) : Fintype.card {y // R x y} = 0 ∨ Fintype.card {y // R x y} = 4 := by
    rw [row_eq]
    exact (huT.nonseed_incidence_row_counts E hEn A hA hEA x x.property.1 x.property.2).2
  have hcol (y : Y) : Fintype.card {x // R x y} = 1 ∨ Fintype.card {x // R x y} = 3 := by
    rw [col_eq]
    exact (h.nonseed_incidence_column_counts huT E A hA hEA hAQ hpure y y.property.1 y.property.2).2.2
  have huni (x y : X) : Fintype.card {b // R x b} = Fintype.card {b // R y b} := by
    have hx1 : (x : G) ≠ 1 := fun he => x.property.2 (he ▸ (zpowers u).one_mem)
    have hy1 : (y : G) ≠ 1 := fun he => y.property.2 (he ▸ (zpowers u).one_mem)
    have hxu : (x : G) ≠ u := fun he => x.property.2 (by rw [he]; exact mem_zpowers u)
    have hyu : (y : G) ≠ u := fun he => y.property.2 (by rw [he]; exact mem_zpowers u)
    obtain ⟨g, hg, hxy⟩ := hinner x x.property.1 hx1 hxu y y.property.1 hy1 hyu
    have hcards : Nat.card (A ⊓ (involutionCentralizer (x : G)).pCoreIn 2 : Subgroup G) =
        Nat.card (A ⊓ (involutionCentralizer (y : G)).pCoreIn 2 : Subgroup G) := by
      rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
        pointCore_intersection_conjugate A x g hg.2, hxy]
    rw [row_eq, row_eq,
      (huT.nonseed_incidence_row_counts E hEn A hA hEA x x.property.1 x.property.2).1,
      (huT.nonseed_incidence_row_counts E hEn A hA hEA y y.property.1 y.property.2).1,
      hcards]
  obtain ⟨hr4, hc3⟩ := FiniteIncidence.six_eight_degrees R hX hY hrow hcol huni
  intro x hx hx1
  by_cases hxE : x ∈ E.val
  · by_cases hxu : x = u
    · rw [hxu, hAQ]
      exact E.property.2.2.2
    have hxU : x ∉ zpowers u := by
      intro hh
      rw [mem_zpowers_iff_mem_range_orderOf, huT.involution] at hh
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
      have hn2 : n < 2 := Finset.mem_range.mp hn
      interval_cases n
      · exact hx1 (by simp)
      · exact hxu (by simp)
    let xx : X := ⟨x, hxE, hxU⟩
    have hh := hr4 xx
    rw [row_eq, (huT.nonseed_incidence_row_counts E hEn A hA hEA x hxE hxU).1] at hh
    have hb := h.elementary_sixteen_conjugate_point_core_card A hA x hx (hpure x hx hx1)
    rcases hb with hb | hb <;> omega
  · let yy : Y := ⟨x, hx, hxE⟩
    have hh := hc3 yy
    rw [col_eq] at hh
    obtain ⟨hc, hd, _⟩ := h.nonseed_incidence_column_counts huT E A hA hEA hAQ hpure x hx hxE
    rw [hc] at hh
    omega

/-- Every point of the constructed pure sixteen has an actual eight as its
intersection with its original point core; all earlier markings are retained. -/
theorem TypeAt.exists_all_point_core_eights (h : TypeAt z V) :
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
      (∀ F : Subgroup G,
        (E.val ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  obtain ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768, hc4, hc2, hcZ,
    hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN,
    hCA, hCB, hAQ, hBQ, horbit, hpure, hinner, hall⟩ :=
    h.exists_inner_transitive_nonseed_extensions
  let := hAe
  have hpoints := all_point_intersections_eight h huT E hEn _ hA16 le_sup_left hAQ hpure hinner
  exact ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768, hc4, hc2, hcZ,
    hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN,
    hCA, hCB, hAQ, hBQ, horbit, hpure, hinner, hpoints, hall⟩

end CFSG.Quasithin.HigmanSims
