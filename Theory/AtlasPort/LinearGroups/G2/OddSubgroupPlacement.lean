module

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup

/-!
# Conjugating odd prime subgroups of the G₂ Borel into the split torus

The split torus has index q⁶ in the Borel. Thus, in characteristic two,
every Sylow subgroup for an odd prime in the torus is Sylow in the Borel.
Sylow conjugacy inside the Borel puts any odd prime subgroup into the torus
while preserving the positive-root Sylow two-subgroup.

This isolates the prime-independent argument from the saved G₂ source-action
work in `InvariantLarge/EvenActions/G2/Source/Model.lean`; in particular it
applies at three and does not use the p > 3 classification of A.3.15.
Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511.
The root-defined Borel and its order come from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Atlas.G2.LieParabolicSetup
open scoped Pointwise
namespace Atlas.G2.OddSubgroupPlacement
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem conjugate_pSubgroup_into (H B : Subgroup G)
    (hH : ¬ p ∣ H.index) (hB : IsPGroup p B) :
    ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := H)
  have hm : ¬ p ∣ ((P : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index hH
  let Q : Sylow p G := (P.isPGroup'.map H.subtype).toSylow hm
  obtain ⟨R, hR⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R Q
  refine ⟨g, ?_⟩
  have hmap : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg Sylow.toSubgroup hg
  exact (map_mono hR).trans (hmap ▸ map_subtype_le (P : Subgroup H))

variable {E : Type*} [Field E] [Finite E] [CharP E 2]

omit [CharP E 2] in
theorem torus_index_in_borel :
    ((splitTorus (K := E)).subgroupOf borel).index = Nat.card E ^ 6 := by
  have hc := ((splitTorus (K := E)).subgroupOf borel).card_mul_index
  have ht : Nat.card ((splitTorus (K := E)).subgroupOf borel) = Nat.card (splitTorus (K := E)) :=
    Nat.card_congr (subgroupOfEquivOfLe (show splitTorus (K := E) ≤ borel from le_sup_right)).toEquiv
  rw [ht, card_splitTorus, card_borel] at hc
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.sub_pos_of_lt Finite.one_lt_card) 2)
    (hc.trans (Nat.mul_comm _ _))

theorem conjugate_borel_pSubgroup_into_torus (B : Subgroup (Model E))
    (hB : IsPGroup p B) (hp : p ≠ 2) (hBb : B ≤ borel) :
    ∃ g ∈ borel (K := E), B.map (MulAut.conj g).toMonoidHom ≤ splitTorus := by
  have hnot : ¬ p ∣ 2 := by
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  have hind : ¬ p ∣ ((splitTorus (K := E)).subgroupOf borel).index := by
    rw [torus_index_in_borel]
    obtain ⟨n, _, hn⟩ := field_card (F := E)
    rw [hn]
    intro h
    exact hnot (Nat.Prime.dvd_of_dvd_pow Fact.out (Nat.Prime.dvd_of_dvd_pow Fact.out h))
  have hPB : IsPGroup p (B.subgroupOf borel) :=
    hB.of_injective (subgroupOfEquivOfLe hBb).toMonoidHom (subgroupOfEquivOfLe hBb).injective
  obtain ⟨g, hg⟩ := conjugate_pSubgroup_into (splitTorus.subgroupOf borel)
    (B.subgroupOf borel) hind hPB
  refine ⟨g, g.property, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact hg (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (show (⟨b, hBb hb⟩ : borel (K := E)) ∈ B.subgroupOf borel from hb))
end Atlas.G2.OddSubgroupPlacement
