module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddFixedPoints
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
/-!
# The literal odd commutator is the block Sylow subgroup

In an even natural block whose two-core is its U-layer, a nontrivial odd
torus generates a full Sylow subgroup by commutators. If the ambient
normalizing two-group contains that Sylow and is normalized by the torus,
the larger ambient commutator is exactly the same Sylow intersection.

This keeps S₁=[S,D₁] literal in Aschbacher–Smith 10.2.3(4), p.747.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The source commutator agrees with the full block Sylow intersection. -/
theorem IsL2EvenBlock.ambient_odd_commutator_sylow (K S D : Subgroup G) {n : ℕ} (hK : IsL2EvenBlock K n)
    (hcore : pCore 2 K = blockU K)
    (hSP : Chapter1.IsSylowIn 2 (S ⊓ K) K)
    (hDK : D ≤ K) (hD : Odd (Nat.card D)) (hDn : D ≠ ⊥)
    (hDS : D ≤ normalizer (S : Set G)) (hSK : S ≤ normalizer (K : Set G)) :
    ⁅S,D⁆ = S ⊓ K ∧ Chapter1.IsSylowIn 2 ⁅S,D⁆ K := by
  obtain ⟨P,hP⟩ := hSP
  have hD' : Odd (Nat.card (D.subgroupOf K)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv]
  have hne : D.subgroupOf K ≠ ⊥ := by
    intro he
    apply hDn
    simpa only [map_subgroupOf_eq_of_le hDK,Subgroup.map_bot] using congrArg (map K.subtype) he
  have hn : D.subgroupOf K ≤ normalizer (P : Set K) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hDK,hP,commutator_comm]
    exact le_inf
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hDS))
      ((commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hDK.trans K.le_normalizer)))
  have he : ⁅S ⊓ K,D⁆ = S ⊓ K := by
    have he := congrArg (map K.subtype)
      (hK.sylow_odd_commutator_eq hcore P (D.subgroupOf K) hD' hne hn)
    simpa only [map_commutator,hP,map_subgroupOf_eq_of_le hDK] using he
  have heq : ⁅S,D⁆ = S ⊓ K := by
    apply le_antisymm
    · exact le_inf (le_normalizer_iff_commutator_le_left.mp hDS)
        ((commutator_mono le_rfl hDK).trans
          (le_normalizer_iff_commutator_le_right.mp hSK))
    · rw [←he]
      exact commutator_mono inf_le_left le_rfl
  exact ⟨heq,heq ▸ ⟨P,hP⟩⟩
/-- Relative subnormality discharges the full block Sylow premise. -/
theorem IsL2EvenBlock.ambient_odd_commutator_sylow_of_subnormal
    (K S D H : Subgroup G) {n : ℕ} (hK : IsL2EvenBlock K n)
    (hcore : pCore 2 K = blockU K) (hS : Chapter1.IsSylowIn 2 S H)
    (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal)
    (hDK : D ≤ K) (hD : Odd (Nat.card D)) (hDn : D ≠ ⊥)
    (hDS : D ≤ normalizer (S : Set G)) (hSK : S ≤ normalizer (K : Set G)) :
    ⁅S,D⁆ = S ⊓ K ∧ Chapter1.IsSylowIn 2 ⁅S,D⁆ K :=
  IsL2EvenBlock.ambient_odd_commutator_sylow K S D hK hcore
    (Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hKH hsub)
    hDK hD hDn hDS hSK
end CFSG.Quasithin.ChapterC
