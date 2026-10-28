module

public import Theory.Mathieu.M22.Properties.PairRecognition
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Parabolics

/-!
# Conjugacy of incident pair–hexad flags in M₂₂

Three-transitivity and the unique hexad through three points carry the
standard incident pair and hexad to any incident pair and hexad. Conjugation
therefore identifies their literal stabilizer intersections, of order 384.

This is the native incidence used in the intersection argument for
Aschbacher–Smith I.2.2(6a), printed p.412. The ambient pointwise kernel and
the pair stabilizer's two-core are not identified.
-/

public section
namespace Sporadic.Mathieu
open Subgroup MulAction
open scoped Pointwise

/-- A fixed native pair outside the standard hexad, for the second relative
position needed by central-cover calculations. -/
@[expose] def m22DisjointPair04 : Finset (Fin 22) := {0, 4}

theorem m22DisjointPair04_card : m22DisjointPair04.card = 2 := by decide +kernel

theorem m22DisjointPair04_disjoint : Disjoint m22DisjointPair04 m22Hexad123 := by
  decide +kernel

/-- The actual pair subgroup used for a disjoint-pair model calculation. -/
@[expose] noncomputable def m22DisjointPairStabilizer : Subgroup M22 :=
  stabilizer M22 m22DisjointPair04

/-- Every source-sized subgroup can be put in this specified disjoint-pair
position. The conjugator is shared by both stabilizers. -/
theorem m22_card1920_disjoint_flag (H : Subgroup M22) (hc : Nat.card H = 1920) :
    ∃ g : M22, H = m22DisjointPairStabilizer.map (MulAut.conj g).toMonoidHom ∧
      g • m22Hexad123 ∈ m22Blocks ∧
      Disjoint (g • m22DisjointPair04) (g • m22Hexad123) ∧
      (m22HexadStabilizer ⊓ m22DisjointPairStabilizer).map
          (MulAut.conj g).toMonoidHom = stabilizer M22 (g • m22Hexad123) ⊓ H := by
  obtain ⟨S, hS, hH⟩ := m22_card1920_eq_pair_stabilizer H hc
  rcases Finset.card_eq_two.mp hS with ⟨x, y, hxy, rfl⟩
  obtain ⟨g, hg0, hg4⟩ := (is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    (by decide : (0 : Fin 22) ≠ 4) hxy
  have hg : g • m22DisjointPair04 = ({x, y} : Finset (Fin 22)) := by
    rw [m22DisjointPair04, Finset.smul_finset_insert, Finset.smul_finset_singleton,
      ← hg0, ← hg4]
  have he : H = m22DisjointPairStabilizer.map (MulAut.conj g).toMonoidHom := by
    rw [m22DisjointPairStabilizer, ← stabilizer_smul_eq_stabilizer_map_conj, hg, hH]
  refine ⟨g, he, m22_smul_block_mem g m22Hexad123 m22Hexad123_mem, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp ha
    obtain ⟨y, hy, he⟩ := Finset.mem_smul_finset.mp hb
    have hxy : y = x := (MulAction.injective g) he
    exact Finset.disjoint_left.mp m22DisjointPair04_disjoint hx (hxy ▸ hy)
  · rw [map_inf _ _ _ (MulAut.conj g).injective, ← he]
    change (stabilizer M22 m22Hexad123).map _ ⊓ H = _
    rw [← stabilizer_smul_eq_stabilizer_map_conj]

/-- Simultaneous conjugacy of the actual pair and hexad. -/
theorem m22_pair_hexad_flag_conjugacy {S B : Finset (Fin 22)}
    (hS : S.card = 2) (hB : B ∈ m22Blocks) (hSB : S ⊆ B) :
    ∃ g : M22, g • m22Pair12 = S ∧ g • m22Hexad123 = B := by
  classical
  obtain ⟨z, hzB, hzS⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show S.card < B.card by rw [hS, m22Block_card B hB]; decide)
  rcases Finset.card_eq_two.mp hS with ⟨x, y, hxy, rfl⟩
  have hxz : x ≠ z := by intro he; subst z; exact hzS (by simp)
  have hyz : y ≠ z := by intro he; subst z; exact hzS (by simp)
  let source : Fin 3 ↪ Fin 22 := ⟨![1, 2, 3], by decide +kernel⟩
  let target : Fin 3 ↪ Fin 22 := ⟨![x, y, z], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨g, hg⟩ := isMultiplyPretransitive_iff.mp m22_isThreePretransitive source target
  have hgi (i : Fin 3) : g • source i = target i :=
    congrArg (fun e : Fin 3 ↪ Fin 22 => e i) hg
  have hg1 : g • (1 : Fin 22) = x := hgi 0
  have hg2 : g • (2 : Fin 22) = y := hgi 1
  have hg3 : g • (3 : Fin 22) = z := hgi 2
  refine ⟨g, ?_, ?_⟩
  · rw [m22Pair12, Finset.smul_finset_insert, Finset.smul_finset_singleton, hg1, hg2]
  · have hsrc : ({1, 2, 3} : Finset (Fin 22)) ⊆ m22Hexad123 := by decide +kernel
    have hmap := Finset.smul_finset_subset_smul_finset (a := g) hsrc
    have hsmul : g • ({1, 2, 3} : Finset (Fin 22)) = {x, y, z} := by
      rw [Finset.smul_finset_insert, Finset.smul_finset_insert,
        Finset.smul_finset_singleton, hg1, hg2, hg3]
    rw [hsmul] at hmap
    apply m22Blocks_eq_of_common_triple {x, y, z} (g • m22Hexad123) B
      (Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩)
      (m22_smul_block_mem g m22Hexad123 m22Hexad123_mem) hB hmap
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hSB (by simp)
    · exact hSB (by simp)
    · exact hzB

/-- The standard parabolic maps onto the literal intersection, with one common
conjugating element for both geometrical objects. -/
theorem m22_pair_hexad_intersection_conjugacy {S B : Finset (Fin 22)}
    (hS : S.card = 2) (hB : B ∈ m22Blocks) (hSB : S ⊆ B) :
    ∃ g : M22, g • m22Pair12 = S ∧ g • m22Hexad123 = B ∧
      M22SolvableSylow.pairHexad.map (MulAut.conj g).toMonoidHom =
        stabilizer M22 B ⊓ stabilizer M22 S := by
  obtain ⟨g, hgS, hgB⟩ := m22_pair_hexad_flag_conjugacy hS hB hSB
  refine ⟨g, hgS, hgB, ?_⟩
  change (m22HexadStabilizer ⊓ m22PairStabilizer).map _ = _
  rw [map_inf _ _ _ (MulAut.conj g).injective]
  change (stabilizer M22 m22Hexad123).map _ ⊓ (stabilizer M22 m22Pair12).map _ = _
  rw [← stabilizer_smul_eq_stabilizer_map_conj, ← stabilizer_smul_eq_stabilizer_map_conj,
    hgS, hgB]

theorem m22_pair_hexad_intersection_card {S B : Finset (Fin 22)}
    (hS : S.card = 2) (hB : B ∈ m22Blocks) (hSB : S ⊆ B) :
    Nat.card (stabilizer M22 B ⊓ stabilizer M22 S : Subgroup M22) = 384 := by
  obtain ⟨g, _, _, he⟩ := m22_pair_hexad_intersection_conjugacy hS hB hSB
  rw [← he, card_map_of_injective (MulAut.conj g).injective]
  exact M22SolvableSylow.pairHexad_card

end Sporadic.Mathieu
