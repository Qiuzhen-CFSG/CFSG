module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Relabel

/-!
# Transport from the normalizer's five-point permutation image

The source Sylow subgroup maps onto a Sylow subgroup of the actual normalizer
image, which contains A₅. The invariant source flag pulls back without changing
orders. Vector stabilizers pull back to the literal centralizers in N_G(V).
If the two model orbit indices are 10 and 2, the index tower and the odd
index of T in N_G(V) give the local odd index needed in 13.2.6. No assertion
that C_T(v) is Sylow in the global C_G(v) enters this calculation.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation 13.2.1
on p.877 and the local Sylow step in the proof of 13.2.6 on p.879.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry FlagCoordinates
variable {G : Type*} [Group G] {L V : Subgroup G}

theorem Marking.normalizes (s : Marking L V) : L ≤ normalizer (V : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl x hx
  obtain ⟨y, rfl⟩ := s.range_eq.ge hx
  change MulAut.conj l (s.map y) ∈ V
  exact (s.equivariant ⟨l, hl⟩ y.toAdd).symm ▸ map_mem s _

namespace FlagSource
variable {T : Sylow 2 G} {V₁ V₂ : Subgroup G} (d : FlagSource T L V V₁ V₂)

/-- The actual permutation image of N_G(V). -/
abbrev image : Subgroup Perm := d.normalizerAction.range

/-- The image of the supplied Sylow subgroup under the normalizer action. -/
noncomputable def imageSylow [Finite G] : Sylow 2 d.image :=
  (T.subtype d.T_normalizes).mapSurjective d.normalizerAction.rangeRestrict_surjective

/-- The coordinate preimage of an actual source subgroup. -/
def preimage (W : Subgroup G) : Subgroup (Multiplicative Space) := W.comap d.module.map

theorem alternating_le_image : alternatingGroup (Fin 5) ≤ d.image := by
  intro g hg
  obtain ⟨l, hl⟩ := d.module.onto ⟨g, hg⟩
  refine ⟨⟨l, d.module.normalizes l.property⟩, ?_⟩
  rw [d.action_agrees]
  exact congrArg Subtype.val hl

theorem preimage_map (W : Subgroup G) (hW : W ≤ V) :
    (d.preimage W).map d.module.map = W := by
  rw [preimage, map_comap_eq, d.module.range_eq, inf_eq_right.mpr hW]

theorem preimage_card (W : Subgroup G) (hW : W ≤ V) :
    Nat.card (d.preimage W) = Nat.card W := by
  exact (show Nat.card ((d.preimage W).map d.module.map) = Nat.card (d.preimage W) from
    card_map_of_injective d.module.injective).symm.trans
    (congrArg (fun X : Subgroup G => Nat.card X) (d.preimage_map W hW))

theorem preimage_invariant [Finite G] (W : Subgroup G)
    (hW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (p : d.image) (hp : p ∈ d.imageSylow) (x : Multiplicative Space)
    (hx : x ∈ d.preimage W) :
    Multiplicative.ofAdd (rho p.val x.toAdd) ∈ d.preimage W := by
  obtain ⟨t, ht, rfl⟩ := hp
  change d.module.map (Multiplicative.ofAdd (rho (d.normalizerAction t) x.toAdd)) ∈ W
  rw [← d.normalizer_equivariant]
  exact (hW ht (d.module.map x)).mp hx

/-- The model stabilizer pulls back to the literal relative centralizer. -/
theorem stabilizer_comap (x : Space) :
    (normalizer (V : Set G) ⊓ Gv (d.module.map (Multiplicative.ofAdd x))).subgroupOf
      (normalizer (V : Set G)) =
    (stabilizer d.image x).comap d.normalizerAction.rangeRestrict := by
  ext n
  change ((n : G) ∈ normalizer (V : Set G) ∧
      (n : G) ∈ Gv (d.module.map (Multiplicative.ofAdd x))) ↔
    rho (d.normalizerAction n) x = x
  constructor
  · intro h
    apply Multiplicative.ofAdd.injective
    apply d.module.injective
    rw [← d.normalizer_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp h.2)
  · intro h
    refine ⟨n.property, mem_centralizer_singleton_iff.mpr ?_⟩
    apply mul_inv_eq_iff_eq_mul.mp
    have he := d.normalizer_equivariant n x
    rwa [h] at he

/-- Orbit indices 10 and 2 in the action image force the required local odd index.
No global centralizer Sylow statement is used. -/
theorem localIndex_of_coordinate_indices [Finite G] (x : Space)
    (hN : (stabilizer d.image x).index = 10)
    (hT : (stabilizer d.image x).relIndex (d.imageSylow : Subgroup d.image) = 2) :
    ¬ 2 ∣ (Tv (T : Subgroup G) (d.module.map (Multiplicative.ofAdd x))).relIndex
      (normalizer (V : Set G) ⊓ Gv (d.module.map (Multiplicative.ofAdd x))) := by
  let N := normalizer (V : Set G)
  let C := N ⊓ Gv (d.module.map (Multiplicative.ofAdd x))
  let S := Tv (T : Subgroup G) (d.module.map (Multiplicative.ofAdd x))
  have hCN : C ≤ N := inf_le_left
  have hSC : S ≤ C := inf_le_inf d.T_normalizes le_rfl
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hCi : C.relIndex N = 10 := by
    change (C.subgroupOf N).index = 10
    rw [d.stabilizer_comap, index_comap_of_surjective _ d.normalizerAction.rangeRestrict_surjective]
    exact hN
  have hSi : S.relIndex (T : Subgroup G) = 2 := by
    have he : C.relIndex (T : Subgroup G) = 2 := by
      rw [← relIndex_subgroupOf d.T_normalizes, d.stabilizer_comap, relIndex_comap]
      exact hT
    have hsub : C.subgroupOf (T : Subgroup G) = S.subgroupOf (T : Subgroup G) := by
      ext t
      change ((t : G) ∈ N ∧ _) ↔ ((t : G) ∈ (T : Subgroup G) ∧ _)
      exact ⟨fun h => ⟨t.property, h.2⟩, fun h => ⟨d.T_normalizes t.property, h.2⟩⟩
    change (S.subgroupOf (T : Subgroup G)).index = 2
    rw [← hsub]
    exact he
  have hodd : ¬ 2 ∣ (T : Subgroup G).relIndex N :=
    (T.subtype d.T_normalizes).not_dvd_index
  have h₁ := relIndex_mul_relIndex S C N hSC hCN
  have h₂ := relIndex_mul_relIndex S (T : Subgroup G) N hST d.T_normalizes
  rw [hCi] at h₁
  rw [hSi] at h₂
  change ¬ 2 ∣ S.relIndex C
  intro hd
  obtain ⟨k, hk⟩ := hd
  apply hodd
  refine ⟨5 * k, ?_⟩
  omega
end FlagSource
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
