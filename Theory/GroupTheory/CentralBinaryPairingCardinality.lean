module
public import Theory.ElementaryAbelian.BinaryPairingCardinality
public import Theory.GroupAction.QuotientCommutatorPairing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Orders of centralizers from a central binary commutator pairing

Let V contain the center of a finite group G, of order two, and suppose
[V,G] lies in that center. If V and G/D are elementary abelian and D
centralizes V, the commutator pairing V/Z(G) × G/D → Z(G) has trivial
left kernel. Binary duality makes its right map onto the dual of V/Z(G),
so |V| |C_G(V)| = 2 |G|.

This supplies the subgroup centralizer counts used in Parrott,
*A characterization of the Tits' simple group* (1972), pp.673–674.
-/

namespace Subgroup
open scoped IsMulCommutative commutatorElement

/-- The centralizer order attached to a nondegenerate central binary pairing. -/
public theorem card_mul_card_centralizer_of_central_binary_pairing
    {G : Type*} [Group G] [Finite G]
    (D V : Subgroup G) [D.Normal] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (G ⧸ D)]
    (hZV : center G ≤ V) (hZcard : Nat.card (center G) = 2)
    (hcomm : ⁅V, ⊤⁆ ≤ center G) (hDC : D ≤ centralizer (V : Set G)) :
    Nat.card V * Nat.card (centralizer (V : Set G)) = 2 * Nat.card G := by
  classical
  let Z := center G
  let A := V ⧸ Z.subgroupOf V
  let B := G ⧸ D
  let πV : V →* A := QuotientGroup.mk' (Z.subgroupOf V)
  let πG : G →* B := QuotientGroup.mk' D
  let _ : IsElementaryAbelian 2 A := {
    exponent_dvd_p := MonoidHom.exponent_dvd (f := πV) (QuotientGroup.mk'_surjective _)
      |>.trans (IsElementaryAbelian.exponent_dvd_p 2 V) }
  have hbot : (⊥ : Subgroup G).subgroupOf Z = (⊥ : Subgroup Z) := by ext z; simp
  let _ : ((⊥ : Subgroup G).subgroupOf Z).Normal := hbot.symm ▸ inferInstance
  let e0 : (Z ⧸ (⊥ : Subgroup G).subgroupOf Z) ≃* Z :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let eZ : Z ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hZcard (by simp)
  have hZcomm : ⁅Z, (⊤ : Subgroup G)⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_comm, commutator_eq_bot_iff_le_centralizer]
    intro g _ z hz
    exact (mem_center_iff.mp hz g).symm
  let raw := (quotientCommutatorPairing V ⊤ Z ⊥ hZV hcomm hZcomm).compr₂
    (e0.trans eZ).toMonoidHom
  have hraw_one (v : V) (g : (⊤ : Subgroup G)) :
      raw v g = 1 ↔ Commute (v : G) (g : G) := by
    dsimp only [raw]
    rw [MonoidHom.compr₂_apply, quotientCommutatorPairing_apply]
    change eZ (e0 (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf Z) _)) = 1 ↔ _
    change eZ ⟨⁅(v : G), (g : G)⁆, _⟩ = 1 ↔ _
    rw [← eZ.map_one, eZ.injective.eq_iff, Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm
  have hkillZ : Z.subgroupOf V ≤ raw.ker := by
    intro z hz
    ext g
    apply (hraw_one z g).mpr
    exact (mem_center_iff.mp hz g).symm
  let first : A →* ((⊤ : Subgroup G) →* Multiplicative (ZMod 2)) :=
    QuotientGroup.lift (Z.subgroupOf V) raw hkillZ
  let topLift : G →* (⊤ : Subgroup G) := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm
  have hkillD (a : A) : D ≤ ((first a).comp topLift).ker := by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) a
    intro d hd
    change raw v (topLift d) = 1
    exact (hraw_one v (topLift d)).mpr ((hDC hd) v v.property)
  let pairing : A →* (B →* Multiplicative (ZMod 2)) := {
    toFun a := QuotientGroup.lift D ((first a).comp topLift) (hkillD a)
    map_one' := by
      apply MonoidHom.ext
      intro b
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D b
      change first 1 (topLift g) = 1
      simp
    map_mul' a b := by
      apply MonoidHom.ext
      intro c
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D c
      change first (a * b) (topLift g) = first a (topLift g) * first b (topLift g)
      rw [map_mul]
      rfl }
  have hinj : Function.Injective pairing := by
    apply (MonoidHom.ker_eq_bot_iff pairing).mp
    apply bot_unique
    intro a ha
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) a
    apply (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) v).mpr
    apply mem_center_iff.mpr
    intro g
    have hh := congrArg (fun f : B →* Multiplicative (ZMod 2) => f (πG g)) ha
    exact ((hraw_one v (topLift g)).mp hh).symm.eq
  let f := pairing.flip.comp πG
  have hsurj : Function.Surjective f :=
    (MonoidHom.binary_pairing_flip_surjective pairing hinj).comp (QuotientGroup.mk'_surjective D)
  have hker : f.ker = centralizer (V : Set G) := by
    ext g
    constructor
    · intro hg v hv
      have hh := congrArg (fun l : A →* Multiplicative (ZMod 2) => l (πV ⟨v, hv⟩)) hg
      exact ((hraw_one ⟨v, hv⟩ (topLift g)).mp hh).eq
    · intro hg
      apply MonoidHom.ext
      intro a
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) a
      exact (hraw_one v (topLift g)).mpr (hg v v.property)
  have hindex : (centralizer (V : Set G)).index = Nat.card A := by
    rw [← hker, index_ker, f.range_eq_top.mpr hsurj, card_top, MonoidHom.binary_dual_card]
  have hVcard : Nat.card A * 2 = Nat.card V := by
    have hc := (Z.subgroupOf V).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv, hZcard] at hc
    exact hc
  have hc := (centralizer (V : Set G)).index_mul_card
  rw [hindex] at hc
  rw [← hVcard, ← hc]
  ring

end Subgroup
