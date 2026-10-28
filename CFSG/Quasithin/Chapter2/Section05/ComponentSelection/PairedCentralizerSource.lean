module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallFourExistence
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.TwoComponentCenterSource
public import Theory.GroupTheory.QuasithinPairCentralizer
/-!
# The three-prime centralizer of the actual two-component orbit

A constructed four-group in the source component has S₄ normalizer. The
normalizer of this four-group in G is genuinely two-local; together with
the commuting component it exhausts its permitted three-rank. Therefore
the centralizer of K₀ has three-prime order in the nonnormal branch.
No rank bound on N_G(K) or chosen four-group is assumed.

Source: Aschbacher--Smith 2.5.20, first residual calculation, printed p.564.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The literal centralizer of a commuting conjugate pair has three-prime order. -/
theorem MathieuSourceSetup.companion_centralizer_coprime_three
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel L) (u : G)
    (hcomm : L ≤ centralizer (L.conjBy u : Set G)) :
    Nat.Coprime 3 (Nat.card (centralizer ((L ⊔ L.conjBy u : Subgroup G) : Set G))) := by
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  obtain ⟨F, hF, ⟨eF⟩⟩ := hm.exists_symmetric_four
  let : IsKleinFour F := hF
  let e : L.conjBy u ≃* L := ((MulAut.conj u).subgroupMap L).symm
  have hz : center (L.conjBy u) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center L := (centerCongr e ⟨x, hx⟩).property
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen, mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hd : 3 ∣ Nat.card (L.conjBy u) := by
    rw [Nat.card_congr e.toEquiv]
    exact hm.three_dvd_card
  exact pair_centralizer_coprime_three_of_four_normalizer hG.quasithin L (L.conjBy u)
    F eF hcomm hz hd

/-- The original nonnormal source component supplies its companion internally. -/
theorem MathieuSourceSetup.nonnormal_orbit_centralizer_coprime_three
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel L)
    (hn : ¬ (L.subgroupOf H).Normal) :
    Nat.Coprime 3 (Nat.card (centralizer
      (componentOrbit L ((S : Subgroup H).map H.subtype) : Set G))) := by
  let Y := (S : Subgroup H).map H.subtype
  have hi := (source_component_normal_or_index_two hG.quasithin c.gamma
    ⟨c.component_le, c.component⟩).resolve_left hn
  obtain ⟨u, hu, hc, ho⟩ := TwoComponentCenter.exists_two_component_orbit
    H L c.component_le c.component S hi
  have he : componentOrbit L Y = L ⊔ L.conjBy u := by
    apply le_antisymm
    · unfold componentOrbit
      apply iSup_le
      intro a
      rcases ho a a.property with he | he
      · rw [he]
        exact le_sup_left
      · rw [he]
        exact le_sup_right
    · apply sup_le
      · exact le_componentOrbit L Y
      · exact le_iSup_of_le (⟨u, hu⟩ : Y) le_rfl
  rw [he]
  exact MathieuSourceSetup.companion_centralizer_coprime_three c hG hempty hgen hb u hc
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
