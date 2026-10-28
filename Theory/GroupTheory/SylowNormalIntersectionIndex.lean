module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Indices in normal intersections and two-core quotients

If S ≤ M ≤ KS with K normal, restriction to K preserves [M:S].
The proof compares the two quotient images and cancels the common index
in the subgroup-index multiplication formula. Two-group kernels likewise
preserve the index of a supplied Sylow two-subgroup. In particular a
core quotient of order 1008 gives Sylow index 63.

Source application: Aschbacher--Smith, the literal component/parabolic
intersection in the proof of 12.5.8(1), printed p.820.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Restriction to a normal factor preserves the index of a supplement. -/
theorem normal_intersection_relIndex (S M K : Subgroup G) [K.Normal]
    (hSM : S ≤ M) (hM : M ≤ K ⊔ S) :
    (S.subgroupOf K).relIndex (M.subgroupOf K) = S.relIndex M := by
  let q := QuotientGroup.mk' K
  have hm : M.map q = S.map q := by
    apply le_antisymm
    · have hh := map_mono (f := q) hM
      simpa only [q, map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] using hh
    · exact map_mono hSM
  have hk : K.relIndex M = K.relIndex S := by
    rw [← QuotientGroup.ker_mk' K, relIndex_ker, relIndex_ker, hm]
  have hi := relIndex_inf_mul_relIndex S K M
  have hj := relIndex_mul_relIndex (S ⊓ K) S M inf_le_left hSM
  rw [inf_relIndex_left, ← hk, ← hi] at hj
  have he : S.relIndex (K ⊓ M) = S.relIndex M :=
    (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (K.subgroupOf M).index_ne_zero_of_finite) (show S.relIndex (K ⊓ M) * K.relIndex M =
      S.relIndex M * K.relIndex M by simpa only [Nat.mul_comm] using hj.symm))
  rw [subgroupOf, relIndex_comap, subgroupOf_map_subtype, inf_comm]
  exact he

end Subgroup
namespace Sylow
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite H] in
/-- A two-group kernel preserves the index of the supplied Sylow subgroup. -/
theorem index_map_of_two_kernel (S : Sylow 2 G) (f : G →* H)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    (S.mapSurjective hf).index = S.index :=
  (S : Subgroup G).index_map_eq hf (hk.le_sylow_of_normal S)

/-- The original SL₂(2) × SL₃(2) quotient gives Sylow index 63. -/
theorem index_eq_sixtyThree_of_core_card (S : Sylow 2 G)
    (hc : Nat.card (G ⧸ pCore 2 G) = 1008) : S.index = 63 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let U := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hi : U.index = S.index := S.index_map_of_two_kernel q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hcount := (U : Subgroup (G ⧸ pCore 2 G)).index_mul_card
  rw [U.card_eq_multiplicity, hc, hi,
    show (Nat.factorization 1008) 2 = 4 from by decide +kernel] at hcount
  omega
end Sylow
