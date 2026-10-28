module
public import Theory.GroupTheory.BinaryPairingCard
public import Theory.GroupAction.QuotientCommutatorPairing

/-!
# Centralizer orders in a binary central layer

If the center has order two and Z(G)≤A≤Z₂(G), with A commutative,
then |A| |C_G(A)| = 2 |G|. The central commutator pairing A×G→Z(G)
has left kernel Z(G) and right kernel C_G(A); binary double-counting
computes their relative orders. This is the counting argument behind
Parrott (1972), pp.673–674, properties (a)–(c).
-/

namespace Subgroup
open scoped IsMulCommutative commutatorElement

/-- Binary duality for the central commutator pairing restricted to two
subgroups. Neither restricted pairing is required to be nondegenerate. -/
public theorem card_mul_card_centralizer_restrict_of_central_binary_pairing
    {G : Type*} [Group G] [Finite G]
    (A B Z : Subgroup G) [IsMulCommutative A] [IsMulCommutative Z]
    (hZA : Z ≤ A) (hcomm : ⁅A, B⁆ ≤ Z) (hZcomm : ⁅Z, B⁆ ≤ ⊥)
    (hZ : Nat.card Z = 2) :
    Nat.card A * Nat.card ((centralizer (A : Set G)).subgroupOf B) =
      Nat.card B * Nat.card ((centralizer (B : Set G)).subgroupOf A) := by
  have hbot : (⊥ : Subgroup G).subgroupOf Z = (⊥ : Subgroup Z) := by ext z; simp
  let : ((⊥ : Subgroup G).subgroupOf Z).Normal := hbot.symm ▸ inferInstance
  let e0 : (Z ⧸ (⊥ : Subgroup G).subgroupOf Z) ≃* Z :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let f := (quotientCommutatorPairing A B Z ⊥ hZA hcomm hZcomm).compr₂ e0.toMonoidHom
  have hone (a : A) (b : B) : f a b = 1 ↔ Commute (a : G) (b : G) := by
    dsimp only [f]
    rw [MonoidHom.compr₂_apply, quotientCommutatorPairing_apply]
    change (⟨⁅(a : G), (b : G)⁆,
      hcomm (commutator_mem_commutator a.property b.property)⟩ : Z) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm
  have hleft : f.ker = (centralizer (B : Set G)).subgroupOf A := by
    ext a
    change f a = 1 ↔ ∀ b ∈ B, b * (a : G) = (a : G) * b
    constructor
    · intro ha b hb
      exact ((hone a ⟨b, hb⟩).mp (DFunLike.congr_fun ha ⟨b, hb⟩)).symm.eq
    · intro ha
      exact MonoidHom.ext fun b => (hone a b).mpr (ha b b.property).symm
  have hright : f.flip.ker = (centralizer (A : Set G)).subgroupOf B := by
    ext b
    change f.flip b = 1 ↔ ∀ a ∈ A, a * (b : G) = (b : G) * a
    constructor
    · intro hb a ha
      exact ((hone ⟨a, ha⟩ b).mp (DFunLike.congr_fun hb ⟨a, ha⟩)).eq
    · intro hb
      exact MonoidHom.ext fun a => (hone a b).mpr (hb a a.property)
  simpa only [hleft, hright] using MonoidHom.binary_pairing_kernel_card hZ f

/-- A commutative subgroup between the center and second center has
centralizer order complementary to its own order, up to the central factor two. -/
public theorem card_mul_card_centralizer_of_center_two
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [IsMulCommutative A]
    (hZA : center G ≤ A) (hcomm : ⁅A, ⊤⁆ ≤ center G)
    (hZ : Nat.card (center G) = 2) :
    Nat.card A * Nat.card (centralizer (A : Set G)) = 2 * Nat.card G := by
  let Z := center G
  have hbot : (⊥ : Subgroup G).subgroupOf Z = (⊥ : Subgroup Z) := by ext z; simp
  let : ((⊥ : Subgroup G).subgroupOf Z).Normal := hbot.symm ▸ inferInstance
  let e0 : (Z ⧸ (⊥ : Subgroup G).subgroupOf Z) ≃* Z :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hZcomm : ⁅Z, (⊤ : Subgroup G)⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
    exact center_le_centralizer _
  let f := (quotientCommutatorPairing A ⊤ Z ⊥ hZA hcomm hZcomm).compr₂ e0.toMonoidHom
  have happly (a : A) (g : (⊤ : Subgroup G)) :
      f a g = ⟨⁅(a : G), (g : G)⁆,
        hcomm (commutator_mem_commutator a.property g.property)⟩ := by
    dsimp only [f]
    rw [MonoidHom.compr₂_apply, quotientCommutatorPairing_apply]
    rfl
  have hone (a : A) (g : (⊤ : Subgroup G)) :
      f a g = 1 ↔ Commute (a : G) (g : G) := by
    rw [happly, Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm
  have hleft : f.ker = Z.subgroupOf A := by
    ext a
    change f a = 1 ↔ (a : G) ∈ center G
    constructor
    · intro ha
      apply mem_center_iff.mpr
      intro g
      have he : f a ⟨g, mem_top g⟩ = 1 := congrArg (fun k => k ⟨g, mem_top g⟩) ha
      exact ((hone a ⟨g, mem_top g⟩).mp he).symm.eq
    · intro ha
      apply MonoidHom.ext
      intro g
      exact (hone a g).mpr (mem_center_iff.mp ha g).symm
  have hright : f.flip.ker.map (⊤ : Subgroup G).subtype = centralizer (A : Set G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩ a ha
      have he : f ⟨a, ha⟩ x = 1 := congrArg (fun k => k ⟨a, ha⟩) hx
      exact ((hone ⟨a, ha⟩ x).mp he).eq
    · intro hg
      refine ⟨⟨g, mem_top g⟩, ?_, rfl⟩
      apply MonoidHom.ext
      intro a
      exact (hone a ⟨g, mem_top g⟩).mpr (hg a a.property)
  have hl : Nat.card f.ker = 2 := by
    rw [hleft]
    exact (Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv).trans hZ
  have hr : Nat.card f.flip.ker = Nat.card (centralizer (A : Set G)) := by
    rw [← hright, card_map_of_injective (⊤ : Subgroup G).subtype_injective]
  have hc := MonoidHom.binary_pairing_kernel_card hZ f
  rw [hl, hr, Nat.card_congr (topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] at hc
  simpa only [mul_comm] using hc

end Subgroup
