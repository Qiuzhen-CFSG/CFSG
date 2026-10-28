module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NormalizerSixteen
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The original sixteen is the full normalizer two-core

The actual quotient is the six-letter symplectic group, whose two-core
is trivial. Hence the original elementary sixteen is the whole two-core
of its normalizer. The order of the original involution centralizer also
shows that this normalizer is a proper subgroup of the original group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The original sixteen is the full ambient two-core of its normalizer. -/
theorem TypeAt.sixteen_normalizer_twoCore (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    (normalizer (A : Set G)).pCoreIn 2 = A := by
  obtain ⟨_, _, _, _, _, φ, _⟩ :=
    h.sixteen_symplectic_normalizer A hA hCA hpure hpoints
  let N := normalizer (A : Set G)
  let K := A.subgroupOf N
  let e := φ.trans Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  have hq : pCore 2 (N ⧸ K) = ⊥ := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [pCore_map_iso, Subgroup.map_bot, Theory.SpecificGroups.SymmetricSix.s6_twoCore_eq_bot]
  have hK : IsPGroup 2 K :=
    (IsElementaryAbelian.isPGroup 2 A).of_equiv (subgroupOfEquivOfLe A.le_normalizer).symm
  have hle : K ≤ pCore 2 N := le_sSup ⟨inferInstance, hK⟩
  let q := QuotientGroup.mk' K
  have hmap : (pCore 2 N).map q ≤ pCore 2 (N ⧸ K) :=
    le_sSup ⟨(inferInstance : (pCore 2 N).Normal).map q
      (QuotientGroup.mk'_surjective K), pCore_isPGroup.map q⟩
  rw [hq] at hmap
  have hupper : pCore 2 N ≤ K := by
    have hh := (Subgroup.map_eq_bot_iff (pCore 2 N) (f := q)).mp (bot_unique hmap)
    simpa only [q, QuotientGroup.ker_mk'] using hh
  have heq : pCore 2 N = K := le_antisymm hupper hle
  change (pCore 2 N).map N.subtype = A
  rw [heq, subgroupOf_map_subtype, inf_eq_left.mpr A.le_normalizer]

/-- The full normalizer of the original sixteen is a proper subgroup
of the original group. -/
theorem TypeAt.sixteen_normalizer_ne_top (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    normalizer (A : Set G) ≠ ⊤ := by
  intro ht
  have hc := h.sixteen_normalizer_card A hA hCA hpure hpoints
  rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
  have hd := (involutionCentralizer z).card_subgroup_dvd_card
  rw [h.centralizer_card, hc] at hd
  norm_num at hd

end CFSG.Quasithin.HigmanSims
