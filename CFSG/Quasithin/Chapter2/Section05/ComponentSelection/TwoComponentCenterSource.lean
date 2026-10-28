module
public import Theory.GroupTheory.TwoComponentCenter
public import Theory.GroupTheory.MarkedInternalProduct
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CenterActionSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowCenter
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MarkSource
/-!
# The nonnormal component branch of the original Sylow center split

The original source setup supplies the index-two component normalizer,
the order-two component Sylow center, and innerness of each actual central
Sylow action. The two-component orbit theorem constructs the central
diagonal projection of the original mark. The actual orbit centralizer is
the original two-core, giving 2.5.8(4) with its prescribed subgroups and mark.
Source: Aschbacher--Smith, printed pp.556--557.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Source 2.5.8(4) for the original nonnormal component and marked involution. -/
theorem MathieuSourceSetup.nonnormal_component_center_split
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel L)
    (hn : ¬ (L.subgroupOf H).Normal) :
    let Y := (S : Subgroup H).map H.subtype
    let D := componentOrbit L Y
    let Z := centerIn Y
    Z = (Z ⊓ D) ⊔ (Z ⊓ twoCore H) ∧
    Disjoint (Z ⊓ D) (Z ⊓ twoCore H) ∧
    Nat.card ↥(Z ⊓ D) = 2 ∧
    Nonempty (Z ≃* ↥(Z ⊓ D) × ↥(Z ⊓ twoCore H)) ∧
    ∃ d : G, orderOf d = 2 ∧ Z ⊓ D = zpowers d ∧
      d⁻¹ * z ∈ Z ⊓ twoCore H := by
  let Y := (S : Subgroup H).map H.subtype
  let P := Y.subgroupOf L
  let T := (center P).map (L.subtype.comp P.subtype)
  let D := componentOrbit L Y
  let Z := centerIn Y
  have hindex : (normalizer (L.subgroupOf H : Set H)).index = 2 :=
    (source_component_normal_or_index_two hG.quasithin c.gamma
      ⟨c.component_le, c.component⟩).resolve_left hn
  obtain ⟨s, hs, hc, horbit⟩ := TwoComponentCenter.exists_two_component_orbit
    H L c.component_le c.component S hindex
  have hTK : T ≤ L := by
    rintro _ ⟨t, ht, rfl⟩
    exact (t : L).property
  have hTY : T ≤ Y := by
    rintro _ ⟨t, ht, rfl⟩
    exact t.property
  have hT : Nat.card T = 2 := by
    change Nat.card ((center P).map (L.subtype.comp P.subtype)) = 2
    rw [card_map_of_injective (f := L.subtype.comp P.subtype)
      (fun _ _ he => P.subtype_injective (L.subtype_injective he))]
    exact (MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.2.2.center_card
  have hinner : ∀ y ∈ Y ⊓ centralizer (Y : Set G), ∃ t ∈ T,
      ∀ k ∈ L, y * k * y⁻¹ = t * k * t⁻¹ := by
    intro y hy
    obtain ⟨u, hu, huZ, ha⟩ := MathieuSourceSetup.center_action_inner c hG hempty hgen hb y hy
    refine ⟨u, ?_, ?_⟩
    · exact ⟨⟨u, hu⟩, mem_center_iff.mpr (fun v => Subtype.ext (huZ v v.property)), rfl⟩
    · intro k hk
      exact (ha ⟨k, hk⟩).symm
  let h := c.localSetup hG structural115Input localC129Input_knownSimple
  have hz : z ∈ Y ⊓ centralizer (Y : Set G) := ⟨h.mem_sylow, h.central⟩
  have hzK : z ∉ centralizer (L : Set G) := by
    obtain ⟨t, _, htZ, ha, _⟩ := MathieuSourceSetup.sylow_projection c hG localC129Input_knownSimple hempty
    intro hzK
    apply htZ
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    have he := ha k
    change (t : G) * k * (t : G)⁻¹ = z * (k : G) * z⁻¹ at he
    rw [← hzK k k.property, mul_inv_cancel_right] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨hjoin, hdis, hcard, d, hdne, hd, hzres⟩ :=
    TwoComponentCenter.center_split_of_two_orbit L Y T s z hs
      (MathieuSourceSetup.component_center_eq_bot c hG hempty hgen)
      hc horbit hTK hTY hT hinner hz hzK
  have hZ : (center Y).map Y.subtype = Z := (centerIn_eq_map_center Y).symm
  rw [hZ] at hjoin hdis hcard hd hzres
  have hcore : Y ⊓ centralizer (D : Set G) = twoCore H :=
    generated_orbit_core ⟨c.component_le, c.component⟩ S hgen
  have hZcore : Z ⊓ centralizer (D : Set G) = Z ⊓ twoCore H := by
    rw [← hcore]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.1.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
  rw [hZcore] at hjoin hdis hzres
  have hcZ : Z ⊓ D ≤ centralizer (Z ⊓ twoCore H : Set G) := by
    intro a ha b hb
    exact ha.1.2 b hb.1.1
  obtain ⟨e, _, _⟩ := exists_marked_internalProductEquiv Z (Z ⊓ D) (Z ⊓ twoCore H)
    hjoin.symm hdis hcZ
  have horder : orderOf d = 2 := by
    rw [hd, Nat.card_zpowers] at hcard
    exact hcard
  exact ⟨hjoin, hdis, hcard, ⟨e⟩, d, horder, hd, hzres⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
