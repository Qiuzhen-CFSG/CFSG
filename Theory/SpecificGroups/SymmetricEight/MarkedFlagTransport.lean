module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.PairStructure
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.FullFlagSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Pair normalizers and simultaneous Sylow alignment on eight points

Maximality of the pair stabilizer and one explicit failed conjugation give
the normalizer of its even part. An odd element then supplements that even
part. If an exceptional comparison takes the even nested flag to a binary
Borel, squaring puts every flag element in a two-group; Sylow maximality
identifies the full flag with the checked binary-tree Sylow. Sylow conjugacy
inside the pair stabilizer preserves the middle parabolic during alignment.

The exceptional comparison is an explicit premise of the flag results;
this module does not construct it. The two partitions are the same literal
partitions throughout, with no conjugacy-class labels substituted for them.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.28(3) and 15.3.32(4), printed pp.1131–1133 (PDF pp.1148–1150).
-/

@[expose] public section
open Subgroup

namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

/-- The normalizer of the even pair subgroup is the full pair stabilizer. -/
theorem normalizer_evenPair :
    normalizer (pairStabilizer ⊓ alternatingGroup (Fin 8) : Subgroup S8) = pairStabilizer := by
  have hle : pairStabilizer ≤ normalizer (pairStabilizer ⊓ alternatingGroup (Fin 8) : Subgroup S8) :=
    (le_inf pairStabilizer.le_normalizer
      (le_normalizer_of_normal : pairStabilizer ≤ normalizer (alternatingGroup (Fin 8) : Set S8))).trans
      inf_normalizer_le_normalizer_inf
  apply le_antisymm ?_ hle
  by_contra h
  have ht := pairStabilizer_isCoatom.2 _ (lt_of_le_not_ge hle h)
  have hn : Equiv.swap (1 : Fin 8) 2 ∈
      normalizer (pairStabilizer ⊓ alternatingGroup (Fin 8) : Subgroup S8) := ht ▸ mem_top _
  have hm : Equiv.swap (0 : Fin 8) 1 * Equiv.swap 4 5 ∈
      pairStabilizer ⊓ alternatingGroup (Fin 8) := by
    constructor
    · change Equiv.swap (0 : Fin 8) 1 * Equiv.swap 4 5 ∈ pairStabilizer
      decide
    · simp [Equiv.Perm.mem_alternatingGroup]
  have hc := (mem_normalizer_iff.mp hn _).mp hm
  exact (by decide :
    Equiv.swap (1 : Fin 8) 2 * (Equiv.swap 0 1 * Equiv.swap 4 5) * (Equiv.swap 1 2)⁻¹
      ∉ pairStabilizer) hc.1

/-- Any subgroup of the pair stabilizer containing an odd element supplements its even part. -/
theorem evenPair_sup_of_odd {T : Subgroup S8}
    (hT : T ≤ pairStabilizer) (ho : ¬ T ≤ alternatingGroup (Fin 8)) :
    (pairStabilizer ⊓ alternatingGroup (Fin 8)) ⊔ T = pairStabilizer := by
  obtain ⟨q, hq, hqo⟩ := SetLike.not_le_iff_exists.mp ho
  have hsign : Equiv.Perm.sign q = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h => hqo (Equiv.Perm.mem_alternatingGroup.mpr h))
  apply le_antisymm (sup_le inf_le_left hT)
  intro x hx
  by_cases hxa : x ∈ alternatingGroup (Fin 8)
  · exact mem_sup_left ⟨hx, hxa⟩
  · have hxsign : Equiv.Perm.sign x = -1 :=
      (Int.units_eq_one_or _).resolve_left (fun h => hxa (Equiv.Perm.mem_alternatingGroup.mpr h))
    have hmem : x * q⁻¹ ∈ pairStabilizer ⊓ alternatingGroup (Fin 8) := by
      refine ⟨pairStabilizer.mul_mem hx (pairStabilizer.inv_mem (hT hq)), ?_⟩
      change x * q⁻¹ ∈ alternatingGroup (Fin 8)
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hxsign, hsign]
      decide
    simpa only [inv_mul_cancel_right] using
      ((pairStabilizer ⊓ alternatingGroup (Fin 8)) ⊔ T).mul_mem
        (mem_sup_left hmem) (mem_sup_right hq)
end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals


namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic

/-- A marked binary Borel makes the entire permutation flag stabilizer a two-group. -/
theorem flag_isPGroup_of_borel
    (e : alternatingGroup (Fin 8) ≃* LinearGroup 4) (b : Basis 3)
    (he : (flagStabilizer.subgroupOf (alternatingGroup (Fin 8))).map e.toMonoidHom =
      cutStabilizer b Set.univ) : IsPGroup 2 flagStabilizer := by
  have hp := (fullFlag_isPGroup b).comap_of_injective e.toMonoidHom e.injective
  rw [← he, comap_map_eq_self_of_injective e.injective] at hp
  intro x
  have hx : x.val ^ 2 ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_pow, Int.units_sq]
  let y : flagStabilizer.subgroupOf (alternatingGroup (Fin 8)) :=
    ⟨⟨x.val ^ 2, hx⟩, flagStabilizer.pow_mem x.property 2⟩
  obtain ⟨k, hk⟩ := hp y
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' := congrArg (fun z : flagStabilizer.subgroupOf (alternatingGroup (Fin 8)) =>
    ((z : alternatingGroup (Fin 8)) : S8)) hk
  change (x.val ^ 2) ^ (2 ^ k) = 1 at hk'
  change x.val ^ (2 ^ (k + 1)) = 1
  rwa [pow_succ', pow_mul]

/-- The marked flag is exactly the existing binary-tree Sylow subgroup. -/
theorem flag_eq_tree_of_borel
    (e : alternatingGroup (Fin 8) ≃* LinearGroup 4) (b : Basis 3)
    (he : (flagStabilizer.subgroupOf (alternatingGroup (Fin 8))).map e.toMonoidHom =
      cutStabilizer b Set.univ) : flagStabilizer = treeGroup :=
  treeSylow.is_maximal' (flag_isPGroup_of_borel e b he) treeGroup_le_flagStabilizer

/-- Conjugation inside the pair stabilizer aligns any contained Sylow with the literal flag. -/
theorem sylow_pair_alignment_of_borel
    (e : alternatingGroup (Fin 8) ≃* LinearGroup 4) (b : Basis 3)
    (he : (flagStabilizer.subgroupOf (alternatingGroup (Fin 8))).map e.toMonoidHom =
      cutStabilizer b Set.univ)
    (T : Sylow 2 S8) (hT : (T : Subgroup S8) ≤ pairStabilizer) :
    ∃ q ∈ pairStabilizer, (T : Subgroup S8).map (MulAut.conj q).toMonoidHom = flagStabilizer := by
  have htree : (treeSylow : Subgroup S8) ≤ pairStabilizer :=
    treeGroup_le_flagStabilizer.trans inf_le_left
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq pairStabilizer (T.subtype hT) (treeSylow.subtype htree)
  refine ⟨q.val, q.property, ?_⟩
  have hq' : (q.val • T : Sylow 2 S8) = treeSylow := by
    apply Sylow.subtype_injective (hP := Sylow.smul_le hT q) (hQ := htree)
    rwa [← Sylow.smul_subtype]
  change ((q.val • T : Sylow 2 S8) : Subgroup S8) = _
  rw [hq', treeSylow_coe, flag_eq_tree_of_borel e b he]
end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
