module

public import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M22.Properties.Identification
public import Theory.Mathieu.M22.Properties.Transitivity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

open scoped Pointwise

/-- The standard unordered pair in the natural degree-22 action. -/
@[expose] public def m22Pair12 : Finset (Fin 22) := {1, 2}

/-- The setwise stabilizer of the standard unordered pair. -/
@[expose] public noncomputable def m22PairStabilizer : Subgroup M22 :=
  MulAction.stabilizer M22 m22Pair12

private theorem m22Pair12_orbit :
    MulAction.orbit M22 m22Pair12 =
      {S : Finset (Fin 22) | S.card = 2} := by
  ext S
  constructor
  · intro hS
    rcases MulAction.mem_orbit_iff.mp hS with ⟨g, rfl⟩
    simp [m22Pair12]
  · intro hS
    rcases Finset.card_eq_two.mp hS with ⟨x, y, hxy, rfl⟩
    have h12 : (1 : Fin 22) ≠ 2 := by decide +kernel
    rcases (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
        h12 hxy with ⟨g, hg1, hg2⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g, ?_⟩
    rw [m22Pair12, Finset.smul_finset_insert, Finset.smul_finset_singleton]
    rw [← hg1, ← hg2]

private theorem m22Pair12_orbit_card :
    Nat.card (MulAction.orbit M22 m22Pair12) = 231 := by
  let : Fintype (MulAction.orbit M22 m22Pair12) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard, m22Pair12_orbit]
  let pairs : Finset (Finset (Fin 22)) :=
    Finset.univ.powersetCard 2
  have hpairs :
      {S : Finset (Fin 22) | S.card = 2} =
        (pairs : Set (Finset (Fin 22))) := by
    ext S
    simp [pairs]
  rw [hpairs, Set.ncard_coe_finset]
  change (Finset.univ.powersetCard 2).card = 231
  rw [Finset.card_powersetCard]
  decide +kernel

/-- The standard pair stabilizer has order 1920, the order of 2^4:S5. -/
public theorem m22PairStabilizer_card :
    Nat.card m22PairStabilizer = 1920 := by
  let : Fintype (MulAction.orbit M22 m22Pair12) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    M22 m22Pair12
  have hNat :
      Nat.card (MulAction.orbit M22 m22Pair12) *
          Nat.card m22PairStabilizer = Nat.card M22 := by
    simpa only [m22PairStabilizer, Nat.card_eq_fintype_card] using h
  rw [m22Pair12_orbit_card, m22_order] at hNat
  omega

/-- The setwise stabilizer of the standard hexad. -/
@[expose] public noncomputable def m22HexadStabilizer : Subgroup M22 :=
  MulAction.stabilizer M22 m22Hexad123

private theorem m22Hexad123_orbit :
    MulAction.orbit M22 m22Hexad123 =
      (m22Blocks : Set (Finset (Fin 22))) := by
  ext B
  constructor
  · intro hB
    rcases MulAction.mem_orbit_iff.mp hB with ⟨g, rfl⟩
    exact m22_smul_block_mem g m22Hexad123 m22Hexad123_mem
  · intro hB
    have hBcard : B.card = 6 := m22Block_card B hB
    obtain ⟨S, hSB, hScard⟩ :=
      Finset.exists_subset_card_eq (s := B) (n := 3) (by omega)
    rcases Finset.card_eq_three.mp hScard with
      ⟨x, y, z, hxy, hxz, hyz, hS⟩
    have hSB' : ({x, y, z} : Finset (Fin 22)) ⊆ B := by
      rw [← hS]
      exact hSB
    have hScard' : ({x, y, z} : Finset (Fin 22)).card = 3 := by
      rw [← hS]
      exact hScard
    let source : Fin 3 ↪ Fin 22 :=
      ⟨![1, 2, 3], by decide +kernel⟩
    let target : Fin 3 ↪ Fin 22 :=
      ⟨![x, y, z], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all⟩
    rcases (MulAction.isMultiplyPretransitive_iff.mp
      m22_isThreePretransitive source target) with ⟨g, hg⟩
    have hg1 : g • (1 : Fin 22) = x := by
      have hi := congrArg (fun e : Fin 3 ↪ Fin 22 => e 0) hg
      change g • source 0 = target 0 at hi
      rw [show source 0 = (1 : Fin 22) by rfl,
        show target 0 = x by rfl] at hi
      exact hi
    have hg2 : g • (2 : Fin 22) = y := by
      have hi := congrArg (fun e : Fin 3 ↪ Fin 22 => e 1) hg
      change g • source 1 = target 1 at hi
      rw [show source 1 = (2 : Fin 22) by rfl,
        show target 1 = y by rfl] at hi
      exact hi
    have hg3 : g • (3 : Fin 22) = z := by
      have hi := congrArg (fun e : Fin 3 ↪ Fin 22 => e 2) hg
      change g • source 2 = target 2 at hi
      rw [show source 2 = (3 : Fin 22) by rfl,
        show target 2 = z by rfl] at hi
      exact hi
    have hsource :
        ({1, 2, 3} : Finset (Fin 22)) ⊆ m22Hexad123 := by
      decide +kernel
    have hmap :=
      Finset.smul_finset_subset_smul_finset (a := g) hsource
    have hsmul :
        g • ({1, 2, 3} : Finset (Fin 22)) = {x, y, z} := by
      rw [Finset.smul_finset_insert, Finset.smul_finset_insert,
        Finset.smul_finset_singleton, hg1, hg2, hg3]
    rw [hsmul] at hmap
    have hMoved : g • m22Hexad123 ∈ m22Blocks :=
      m22_smul_block_mem g m22Hexad123 m22Hexad123_mem
    have hEq := m22Blocks_eq_of_common_triple
      {x, y, z} (g • m22Hexad123) B hScard' hMoved hB hmap hSB'
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨g, hEq⟩

private theorem m22Hexad123_orbit_card :
    Nat.card (MulAction.orbit M22 m22Hexad123) = 77 := by
  let : Fintype (MulAction.orbit M22 m22Hexad123) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard, m22Hexad123_orbit,
    Set.ncard_coe_finset]
  exact m22Blocks_cardinality

/-- The standard hexad stabilizer has order 5760, the order of 2^4:A6. -/
public theorem m22HexadStabilizer_card :
    Nat.card m22HexadStabilizer = 5760 := by
  let : Fintype (MulAction.orbit M22 m22Hexad123) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    M22 m22Hexad123
  have hNat :
      Nat.card (MulAction.orbit M22 m22Hexad123) *
          Nat.card m22HexadStabilizer = Nat.card M22 := by
    simpa only [m22HexadStabilizer, Nat.card_eq_fintype_card] using h
  rw [m22Hexad123_orbit_card, m22_order] at hNat
  omega

end Sporadic.Mathieu

