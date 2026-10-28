module

public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M22.Basic

open Theory.GroupTheory

namespace Sporadic.Mathieu

open scoped Pointwise

/-- An orbit contained in a finite target bounds a group by the target size times
its point stabilizer. -/
public theorem natCard_le_finsetCard_mul_stabilizer
    {G V : Type*} [Group G] [Fintype G] [Fintype V] [MulAction G V]
    (b : V) (target : Finset V) (horbit : ∀ g : G, g • b ∈ target) :
    Nat.card G ≤ target.card * Nat.card (MulAction.stabilizer G b) := by
  let : Fintype (MulAction.orbit G b) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer G b) := Fintype.ofFinite _
  let toTarget : MulAction.orbit G b → {x // x ∈ target} := fun x =>
    ⟨x.1, by
      rcases MulAction.mem_orbit_iff.mp x.2 with ⟨g, hg⟩
      rw [← hg]
      exact horbit g⟩
  have hToTarget : Function.Injective toTarget := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : {x // x ∈ target} => z.val) hxy
  have hOrbitLe : Fintype.card (MulAction.orbit G b) ≤ target.card := by
    simpa using Fintype.card_le_of_injective toTarget hToTarget
  have hCard := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G b
  calc
    Nat.card G =
        Fintype.card (MulAction.orbit G b) *
          Nat.card (MulAction.stabilizer G b) := by
      simpa only [Nat.card_eq_fintype_card] using hCard.symm
    _ ≤ target.card * Nat.card (MulAction.stabilizer G b) :=
      Nat.mul_le_mul_right _ hOrbitLe

/-- The successive point stabilizers used for the Steiner-defined M22 upper bound. -/
public noncomputable abbrev m22Stab1 : Subgroup M22 :=
  MulAction.stabilizer M22 (1 : Fin 22)
public noncomputable abbrev m22Stab2 : Subgroup m22Stab1 :=
  MulAction.stabilizer m22Stab1 (2 : Fin 22)
public noncomputable abbrev m22Stab3 : Subgroup m22Stab2 :=
  MulAction.stabilizer m22Stab2 (3 : Fin 22)
public noncomputable abbrev m22Stab4 : Subgroup m22Stab3 :=
  MulAction.stabilizer m22Stab3 (4 : Fin 22)
public noncomputable abbrev m22Stab5 : Subgroup m22Stab4 :=
  MulAction.stabilizer m22Stab4 (10 : Fin 22)

public abbrev m22Stab1M22 (g : m22Stab1) : M22 := g
public abbrev m22Stab2M22 (g : m22Stab2) : M22 := (g : m22Stab1)
public abbrev m22Stab3M22 (g : m22Stab3) : M22 := ((g : m22Stab2) : m22Stab1)
public abbrev m22Stab4M22 (g : m22Stab4) : M22 :=
  (((g : m22Stab3) : m22Stab2) : m22Stab1)
public abbrev m22Stab5M22 (g : m22Stab5) : M22 :=
  ((((g : m22Stab4) : m22Stab3) : m22Stab2) : m22Stab1)

public abbrev m22Stab1Perm (g : m22Stab1) : Equiv.Perm (Fin 22) :=
  ((g : M22) : Equiv.Perm (Fin 22))
public abbrev m22Stab2Perm (g : m22Stab2) : Equiv.Perm (Fin 22) :=
  (((g : m22Stab1) : M22) : Equiv.Perm (Fin 22))
public abbrev m22Stab3Perm (g : m22Stab3) : Equiv.Perm (Fin 22) :=
  ((((g : m22Stab2) : m22Stab1) : M22) : Equiv.Perm (Fin 22))
public abbrev m22Stab4Perm (g : m22Stab4) : Equiv.Perm (Fin 22) :=
  (((((g : m22Stab3) : m22Stab2) : m22Stab1) : M22) : Equiv.Perm (Fin 22))
public abbrev m22Stab5Perm (g : m22Stab5) : Equiv.Perm (Fin 22) :=
  ((((((g : m22Stab4) : m22Stab3) : m22Stab2) : m22Stab1) : M22) :
    Equiv.Perm (Fin 22))

public theorem m22Stab1_fix1 (g : m22Stab1) : m22Stab1Perm g 1 = 1 := g.property

public theorem m22Stab2_fix1 (g : m22Stab2) : m22Stab2Perm g 1 = 1 :=
  (g : m22Stab1).property
public theorem m22Stab2_fix2 (g : m22Stab2) : m22Stab2Perm g 2 = 2 := g.property

public theorem m22Stab3_fix1 (g : m22Stab3) : m22Stab3Perm g 1 = 1 :=
  ((g : m22Stab2) : m22Stab1).property
public theorem m22Stab3_fix2 (g : m22Stab3) : m22Stab3Perm g 2 = 2 :=
  (g : m22Stab2).property
public theorem m22Stab3_fix3 (g : m22Stab3) : m22Stab3Perm g 3 = 3 := g.property

public theorem m22Stab4_fix1 (g : m22Stab4) : m22Stab4Perm g 1 = 1 :=
  (((g : m22Stab3) : m22Stab2) : m22Stab1).property
public theorem m22Stab4_fix2 (g : m22Stab4) : m22Stab4Perm g 2 = 2 :=
  ((g : m22Stab3) : m22Stab2).property
public theorem m22Stab4_fix3 (g : m22Stab4) : m22Stab4Perm g 3 = 3 :=
  (g : m22Stab3).property
public theorem m22Stab4_fix4 (g : m22Stab4) : m22Stab4Perm g 4 = 4 := g.property

public theorem m22Stab5_fix1 (g : m22Stab5) : m22Stab5Perm g 1 = 1 :=
  ((((g : m22Stab4) : m22Stab3) : m22Stab2) : m22Stab1).property
public theorem m22Stab5_fix2 (g : m22Stab5) : m22Stab5Perm g 2 = 2 :=
  (((g : m22Stab4) : m22Stab3) : m22Stab2).property
public theorem m22Stab5_fix3 (g : m22Stab5) : m22Stab5Perm g 3 = 3 :=
  ((g : m22Stab4) : m22Stab3).property
public theorem m22Stab5_fix4 (g : m22Stab5) : m22Stab5Perm g 4 = 4 :=
  (g : m22Stab4).property
public theorem m22Stab5_fix10 (g : m22Stab5) : m22Stab5Perm g 10 = 10 := g.property

/-- Two hexads containing the same three-set are equal. -/
public theorem m22Blocks_eq_of_common_triple
    (S B C : Finset (Fin 22)) (hS : S.card = 3)
    (hB : B ∈ m22Blocks) (hC : C ∈ m22Blocks)
    (hSB : S ⊆ B) (hSC : S ⊆ C) : B = C := by
  have hCard := m22Blocks_unique_block S hS
  have hB' : B ∈ m22Blocks.filter (fun E => S ⊆ E) :=
    Finset.mem_filter.mpr ⟨hB, hSB⟩
  have hC' : C ∈ m22Blocks.filter (fun E => S ⊆ E) :=
    Finset.mem_filter.mpr ⟨hC, hSC⟩
  exact (Finset.card_le_one_iff.mp hCard.le) hB' hC'

/-- An element of M22 sends every hexad to a hexad. -/
public theorem m22_smul_block_mem (g : M22) (B : Finset (Fin 22))
    (hB : B ∈ m22Blocks) : (g : Equiv.Perm (Fin 22)) • B ∈ m22Blocks := by
  have hgDesign : (g : Equiv.Perm (Fin 22)) ∈ m22DesignAut :=
    M22_le_m22DesignAut g.property
  rw [m22DesignAut, SteinerSystem.mem_aut_iff] at hgDesign
  have hB' : B ∈ (m22WittDesign.blocks : Set (Finset (Fin 22))) := by
    simpa [m22WittDesign] using hB
  have hImage : (g : Equiv.Perm (Fin 22)) • B ∈
      (g : Equiv.Perm (Fin 22)) • (m22WittDesign.blocks : Set (Finset (Fin 22))) :=
    Set.smul_mem_smul_set hB'
  rw [hgDesign] at hImage
  simpa [m22WittDesign] using hImage

/-- A hexad containing a fixed three-set is fixed setwise. -/
public theorem m22_smul_block_eq_self_of_fixed_triple
    (g : M22) (S B : Finset (Fin 22)) (hS : S.card = 3)
    (hB : B ∈ m22Blocks) (hSB : S ⊆ B)
    (hfix : ∀ x ∈ S, (g : Equiv.Perm (Fin 22)) x = x) :
    (g : Equiv.Perm (Fin 22)) • B = B := by
  apply m22Blocks_eq_of_common_triple S ((g : Equiv.Perm (Fin 22)) • B) B hS
  · exact m22_smul_block_mem g B hB
  · exact hB
  · intro x hx
    have hxB : x ∈ B := hSB hx
    have hImage := Finset.smul_mem_smul_finset
      (a := (g : Equiv.Perm (Fin 22))) hxB
    simpa [hfix x hx] using hImage
  · exact hSB

/-- A permutation cannot send a point to a distinct fixed point. -/
public theorem perm_apply_ne_of_ne_fixed {α : Type*} (g : Equiv.Perm α) {x a : α}
    (hxa : x ≠ a) (hfix : g a = a) : g x ≠ a := by
  intro h
  apply hxa
  exact g.injective (h.trans hfix.symm)

open scoped Pointwise

@[expose] public def m22Hexad123 : Finset (Fin 22) := {1, 2, 3, 10, 18, 20}
@[expose] public def m22Hexad124 : Finset (Fin 22) := {1, 2, 4, 7, 15, 21}
@[expose] public def m22Hexad134 : Finset (Fin 22) := {1, 3, 4, 8, 13, 14}
@[expose] public def m22Hexad14Ten : Finset (Fin 22) := {1, 4, 6, 10, 12, 17}
@[expose] public def m22Hexad234 : Finset (Fin 22) := {2, 3, 4, 6, 11, 22}
@[expose] public def m22Hexad24Ten : Finset (Fin 22) := {2, 4, 9, 10, 14, 16}
@[expose] public def m22Hexad34Ten : Finset (Fin 22) := {3, 4, 5, 7, 10, 19}

public theorem m22BlockAt_mem (i : Fin 77) : m22BlockAt i ∈ m22Blocks := by
  rw [← m22BlockAt_image]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

public theorem m22Hexad123_mem : m22Hexad123 ∈ m22Blocks := by
  rw [← show m22BlockAt 0 = m22Hexad123 by decide +kernel]
  exact m22BlockAt_mem 0
public theorem m22Hexad124_mem : m22Hexad124 ∈ m22Blocks := by
  rw [← show m22BlockAt 1 = m22Hexad124 by decide +kernel]
  exact m22BlockAt_mem 1
public theorem m22Hexad134_mem : m22Hexad134 ∈ m22Blocks := by
  rw [← show m22BlockAt 5 = m22Hexad134 by decide +kernel]
  exact m22BlockAt_mem 5
public theorem m22Hexad14Ten_mem : m22Hexad14Ten ∈ m22Blocks := by
  rw [← show m22BlockAt 10 = m22Hexad14Ten by decide +kernel]
  exact m22BlockAt_mem 10
public theorem m22Hexad234_mem : m22Hexad234 ∈ m22Blocks := by
  rw [← show m22BlockAt 21 = m22Hexad234 by decide +kernel]
  exact m22BlockAt_mem 21
public theorem m22Hexad24Ten_mem : m22Hexad24Ten ∈ m22Blocks := by
  rw [← show m22BlockAt 26 = m22Hexad24Ten by decide +kernel]
  exact m22BlockAt_mem 26
public theorem m22Hexad34Ten_mem : m22Hexad34Ten ∈ m22Blocks := by
  rw [← show m22BlockAt 37 = m22Hexad34Ten by decide +kernel]
  exact m22BlockAt_mem 37

public theorem m22Stab3_smul_hexad123 (g : m22Stab3) :
    m22Stab3Perm g • m22Hexad123 = m22Hexad123 := by
  apply m22_smul_block_eq_self_of_fixed_triple
    (m22Stab3M22 g) {1, 2, 3} m22Hexad123
  · decide +kernel
  · exact m22Hexad123_mem
  · decide +kernel
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact m22Stab3_fix1 g
    · exact m22Stab3_fix2 g
    · exact m22Stab3_fix3 g

public theorem m22Stab4_smul_hexad123 (g : m22Stab4) :
    m22Stab4Perm g • m22Hexad123 = m22Hexad123 := by
  apply m22_smul_block_eq_self_of_fixed_triple
    (m22Stab4M22 g) {1, 2, 3} m22Hexad123
  · decide +kernel
  · exact m22Hexad123_mem
  · decide +kernel
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact m22Stab4_fix1 g
    · exact m22Stab4_fix2 g
    · exact m22Stab4_fix3 g

private theorem m22Stab5_smul_hexad_of_fixed_triple
    (g : m22Stab5) (a b c : Fin 22) (B : Finset (Fin 22))
    (hcard : ({a, b, c} : Finset (Fin 22)).card = 3)
    (hB : B ∈ m22Blocks) (hsub : {a, b, c} ⊆ B)
    (ha : m22Stab5Perm g a = a) (hb : m22Stab5Perm g b = b)
    (hc : m22Stab5Perm g c = c) : m22Stab5Perm g • B = B := by
  apply m22_smul_block_eq_self_of_fixed_triple
    (m22Stab5M22 g) {a, b, c} B
  · exact hcard
  · exact hB
  · exact hsub
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc

public theorem m22Stab5_smul_hexad123 (g : m22Stab5) :
    m22Stab5Perm g • m22Hexad123 = m22Hexad123 := by
  apply m22Stab5_smul_hexad_of_fixed_triple g 1 2 3
  · decide +kernel
  · exact m22Hexad123_mem
  · decide +kernel
  · exact m22Stab5_fix1 g
  · exact m22Stab5_fix2 g
  · exact m22Stab5_fix3 g

public theorem m22Stab5_smul_hexad124 (g : m22Stab5) :
    m22Stab5Perm g • m22Hexad124 = m22Hexad124 := by
  apply m22Stab5_smul_hexad_of_fixed_triple g 1 2 4
  · decide +kernel
  · exact m22Hexad124_mem
  · decide +kernel
  · exact m22Stab5_fix1 g
  · exact m22Stab5_fix2 g
  · exact m22Stab5_fix4 g

public theorem m22Stab5_smul_hexad134 (g : m22Stab5) :
    m22Stab5Perm g • m22Hexad134 = m22Hexad134 := by
  apply m22Stab5_smul_hexad_of_fixed_triple g 1 3 4
  · decide +kernel
  · exact m22Hexad134_mem
  · decide +kernel
  · exact m22Stab5_fix1 g
  · exact m22Stab5_fix3 g
  · exact m22Stab5_fix4 g

public theorem m22Stab5_smul_hexad14Ten (g : m22Stab5) :
    m22Stab5Perm g • m22Hexad14Ten = m22Hexad14Ten := by
  apply m22Stab5_smul_hexad_of_fixed_triple g 1 4 10
  · decide +kernel
  · exact m22Hexad14Ten_mem
  · decide +kernel
  · exact m22Stab5_fix1 g
  · exact m22Stab5_fix4 g
  · exact m22Stab5_fix10 g

public theorem m22Stab5_smul_hexad234 (g : m22Stab5) :
    m22Stab5Perm g • m22Hexad234 = m22Hexad234 := by
  apply m22Stab5_smul_hexad_of_fixed_triple g 2 3 4
  · decide +kernel
  · exact m22Hexad234_mem
  · decide +kernel
  · exact m22Stab5_fix2 g
  · exact m22Stab5_fix3 g
  · exact m22Stab5_fix4 g

public theorem m22Stab5_smul_hexad24Ten (g : m22Stab5) :
    m22Stab5Perm g • m22Hexad24Ten = m22Hexad24Ten := by
  apply m22Stab5_smul_hexad_of_fixed_triple g 2 4 10
  · decide +kernel
  · exact m22Hexad24Ten_mem
  · decide +kernel
  · exact m22Stab5_fix2 g
  · exact m22Stab5_fix4 g
  · exact m22Stab5_fix10 g

public theorem m22Stab5_smul_hexad34Ten (g : m22Stab5) :
    m22Stab5Perm g • m22Hexad34Ten = m22Hexad34Ten := by
  apply m22Stab5_smul_hexad_of_fixed_triple g 3 4 10
  · decide +kernel
  · exact m22Hexad34Ten_mem
  · decide +kernel
  · exact m22Stab5_fix3 g
  · exact m22Stab5_fix4 g
  · exact m22Stab5_fix10 g

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


public theorem m22_card_le_22_mul_stab1 :
    Nat.card M22 ≤ 22 * Nat.card m22Stab1 := by
  simpa using natCard_le_finsetCard_mul_stabilizer
    (G := M22) (1 : Fin 22) Finset.univ (fun _ => Finset.mem_univ _)

public theorem m22_stab1_card_le_21_mul_stab2 :
    Nat.card m22Stab1 ≤ 21 * Nat.card m22Stab2 := by
  have h := natCard_le_finsetCard_mul_stabilizer
    (G := m22Stab1) (2 : Fin 22)
    ((Finset.univ : Finset (Fin 22)).erase 1) (by
      intro g
      change m22Stab1Perm g 2 ∈ (Finset.univ : Finset (Fin 22)).erase 1
      exact Finset.mem_erase.mpr
        ⟨perm_apply_ne_of_ne_fixed (m22Stab1Perm g) (by decide +kernel)
          (m22Stab1_fix1 g), Finset.mem_univ _⟩)
  simpa using h

public theorem m22_stab2_card_le_20_mul_stab3 :
    Nat.card m22Stab2 ≤ 20 * Nat.card m22Stab3 := by
  have h := natCard_le_finsetCard_mul_stabilizer
    (G := m22Stab2) (3 : Fin 22)
    ((Finset.univ : Finset (Fin 22)) \ {1, 2}) (by
      intro g
      change m22Stab2Perm g 3 ∈
        (Finset.univ : Finset (Fin 22)) \ {1, 2}
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hfixed
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfixed
      rcases hfixed with hfixed | hfixed
      · exact perm_apply_ne_of_ne_fixed (m22Stab2Perm g) (by decide +kernel)
          (m22Stab2_fix1 g) hfixed
      · exact perm_apply_ne_of_ne_fixed (m22Stab2Perm g) (by decide +kernel)
          (m22Stab2_fix2 g) hfixed)
  rw [show ((Finset.univ : Finset (Fin 22)) \ {1, 2}).card = 20 by decide +kernel] at h
  exact h

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

private theorem perm_image_not_mem_of_smul_eq
    (p : Equiv.Perm (Fin 22)) (B : Finset (Fin 22))
    (hB : p • B = B) {x : Fin 22} (hx : x ∉ B) :
    p x ∉ B := by
  intro hpx
  have hpre :
      p⁻¹ (p x) ∈ p⁻¹ • B :=
    Finset.smul_mem_smul_finset (a := p⁻¹) hpx
  have hInv : p⁻¹ • B = B := by
    calc
      p⁻¹ • B = p⁻¹ • (p • B) := by rw [hB]
      _ = B := by simp
  rw [hInv] at hpre
  exact hx (by simpa using hpre)

public theorem m22_stab3_card_le_16_mul_stab4 :
    Nat.card m22Stab3 ≤ 16 * Nat.card m22Stab4 := by
  have h := natCard_le_finsetCard_mul_stabilizer
    (G := m22Stab3) (4 : Fin 22)
    ((Finset.univ : Finset (Fin 22)) \ m22Hexad123) (by
      intro g
      change m22Stab3Perm g 4 ∈
        (Finset.univ : Finset (Fin 22)) \ m22Hexad123
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      exact perm_image_not_mem_of_smul_eq
        (m22Stab3Perm g) m22Hexad123 (m22Stab3_smul_hexad123 g) (by decide +kernel))
  rw [show ((Finset.univ : Finset (Fin 22)) \ m22Hexad123).card = 16 by decide +kernel] at h
  exact h

public theorem m22_stab4_card_le_3_mul_stab5 :
    Nat.card m22Stab4 ≤ 3 * Nat.card m22Stab5 := by
  have h := natCard_le_finsetCard_mul_stabilizer
    (G := m22Stab4) (10 : Fin 22)
    (m22Hexad123 \ {1, 2, 3}) (by
      intro g
      change m22Stab4Perm g 10 ∈ m22Hexad123 \ {1, 2, 3}
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [← m22Stab4_smul_hexad123 g]
        exact Finset.smul_mem_smul_finset (a := m22Stab4Perm g)
          (by decide +kernel : (10 : Fin 22) ∈ m22Hexad123)
      · intro hfixed
        simp only [Finset.mem_insert, Finset.mem_singleton] at hfixed
        rcases hfixed with hfixed | hfixed | hfixed
        · exact perm_apply_ne_of_ne_fixed (m22Stab4Perm g) (by decide +kernel)
            (m22Stab4_fix1 g) hfixed
        · exact perm_apply_ne_of_ne_fixed (m22Stab4Perm g) (by decide +kernel)
            (m22Stab4_fix2 g) hfixed
        · exact perm_apply_ne_of_ne_fixed (m22Stab4Perm g) (by decide +kernel)
            (m22Stab4_fix3 g) hfixed)
  rw [show (m22Hexad123 \ {1, 2, 3}).card = 3 by decide +kernel] at h
  exact h

open scoped Pointwise

private theorem image_mem_of_smul_finset_eq
    (g : Equiv.Perm (Fin 22)) (B : Finset (Fin 22))
    (hB : g • B = B) {x : Fin 22} (hx : x ∈ B) : g x ∈ B := by
  have hImage := Finset.smul_mem_smul_finset (a := g) hx
  rwa [hB] at hImage

public theorem m22Stab5_fix6 (g : m22Stab5) : m22Stab5Perm g 6 = 6 := by
  have h₁ : m22Stab5Perm g 6 ∈ m22Hexad14Ten :=
    image_mem_of_smul_finset_eq _ _ (m22Stab5_smul_hexad14Ten g) (by decide +kernel)
  have h₂ : m22Stab5Perm g 6 ∈ m22Hexad234 :=
    image_mem_of_smul_finset_eq _ _ (m22Stab5_smul_hexad234 g) (by decide +kernel)
  have hmem : m22Stab5Perm g 6 ∈ ({4, 6} : Finset (Fin 22)) := by
    rw [← show m22Hexad14Ten ∩ m22Hexad234 = ({4, 6} : Finset (Fin 22)) by decide +kernel]
    exact Finset.mem_inter.mpr ⟨h₁, h₂⟩
  rcases Finset.mem_insert.mp hmem with h4 | h6
  · exact (perm_apply_ne_of_ne_fixed (m22Stab5Perm g) (by decide +kernel) (m22Stab5_fix4 g) h4).elim
  · simpa only [Finset.mem_singleton] using h6

public theorem m22Stab5_fix7 (g : m22Stab5) : m22Stab5Perm g 7 = 7 := by
  have h₁ : m22Stab5Perm g 7 ∈ m22Hexad124 :=
    image_mem_of_smul_finset_eq _ _ (m22Stab5_smul_hexad124 g) (by decide +kernel)
  have h₂ : m22Stab5Perm g 7 ∈ m22Hexad34Ten :=
    image_mem_of_smul_finset_eq _ _ (m22Stab5_smul_hexad34Ten g) (by decide +kernel)
  have hmem : m22Stab5Perm g 7 ∈ ({4, 7} : Finset (Fin 22)) := by
    rw [← show m22Hexad124 ∩ m22Hexad34Ten = ({4, 7} : Finset (Fin 22)) by decide +kernel]
    exact Finset.mem_inter.mpr ⟨h₁, h₂⟩
  rcases Finset.mem_insert.mp hmem with h4 | h7
  · exact (perm_apply_ne_of_ne_fixed (m22Stab5Perm g) (by decide +kernel) (m22Stab5_fix4 g) h4).elim
  · simpa only [Finset.mem_singleton] using h7

public theorem m22Stab5_fix14 (g : m22Stab5) : m22Stab5Perm g 14 = 14 := by
  have h₁ : m22Stab5Perm g 14 ∈ m22Hexad134 :=
    image_mem_of_smul_finset_eq _ _ (m22Stab5_smul_hexad134 g) (by decide +kernel)
  have h₂ : m22Stab5Perm g 14 ∈ m22Hexad24Ten :=
    image_mem_of_smul_finset_eq _ _ (m22Stab5_smul_hexad24Ten g) (by decide +kernel)
  have hmem : m22Stab5Perm g 14 ∈ ({4, 14} : Finset (Fin 22)) := by
    rw [← show m22Hexad134 ∩ m22Hexad24Ten = ({4, 14} : Finset (Fin 22)) by decide +kernel]
    exact Finset.mem_inter.mpr ⟨h₁, h₂⟩
  rcases Finset.mem_insert.mp hmem with h4 | h14
  · exact (perm_apply_ne_of_ne_fixed (m22Stab5Perm g) (by decide +kernel) (m22Stab5_fix4 g) h4).elim
  · simpa only [Finset.mem_singleton] using h14

@[expose] public def m22Pair011 : Finset (Fin 22) := {0, 11}
@[expose] public def m22Pair519 : Finset (Fin 22) := {5, 19}
@[expose] public def m22Pair813 : Finset (Fin 22) := {8, 13}
@[expose] public def m22Pair916 : Finset (Fin 22) := {9, 16}
@[expose] public def m22Pair1217 : Finset (Fin 22) := {12, 17}
@[expose] public def m22Pair1521 : Finset (Fin 22) := {15, 21}
@[expose] public def m22Pair1820 : Finset (Fin 22) := {18, 20}

private theorem image_mem_sdiff_of_fixed
    (g : Equiv.Perm (Fin 22)) (B fixed : Finset (Fin 22))
    (hB : g • B = B) (hfix : ∀ a ∈ fixed, g a = a)
    {x : Fin 22} (hx : x ∈ B \ fixed) : g x ∈ B \ fixed := by
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact image_mem_of_smul_finset_eq g B hB (Finset.mem_sdiff.mp hx).1
  · intro hgx
    have hggx : g (g x) = g x := hfix (g x) hgx
    have hgxx : g x = x := g.injective hggx
    exact (Finset.mem_sdiff.mp hx).2 (hgxx ▸ hgx)

public theorem m22Stab5_maps_pair011 (g : m22Stab5) {x : Fin 22}
    (hx : x ∈ m22Pair011) : m22Stab5Perm g x ∈ m22Pair011 := by
  rw [← show m22Hexad234 \ {2, 3, 4, 6} = m22Pair011 by decide +kernel] at hx ⊢
  apply image_mem_sdiff_of_fixed (m22Stab5Perm g) m22Hexad234 {2, 3, 4, 6}
  · exact m22Stab5_smul_hexad234 g
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact m22Stab5_fix2 g
    · exact m22Stab5_fix3 g
    · exact m22Stab5_fix4 g
    · exact m22Stab5_fix6 g
  · exact hx

public theorem m22Stab5_maps_pair519 (g : m22Stab5) {x : Fin 22}
    (hx : x ∈ m22Pair519) : m22Stab5Perm g x ∈ m22Pair519 := by
  rw [← show m22Hexad34Ten \ {3, 4, 7, 10} = m22Pair519 by decide +kernel] at hx ⊢
  apply image_mem_sdiff_of_fixed (m22Stab5Perm g) m22Hexad34Ten {3, 4, 7, 10}
  · exact m22Stab5_smul_hexad34Ten g
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact m22Stab5_fix3 g
    · exact m22Stab5_fix4 g
    · exact m22Stab5_fix7 g
    · exact m22Stab5_fix10 g
  · exact hx

public theorem m22Stab5_maps_pair813 (g : m22Stab5) {x : Fin 22}
    (hx : x ∈ m22Pair813) : m22Stab5Perm g x ∈ m22Pair813 := by
  rw [← show m22Hexad134 \ {1, 3, 4, 14} = m22Pair813 by decide +kernel] at hx ⊢
  apply image_mem_sdiff_of_fixed (m22Stab5Perm g) m22Hexad134 {1, 3, 4, 14}
  · exact m22Stab5_smul_hexad134 g
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact m22Stab5_fix1 g
    · exact m22Stab5_fix3 g
    · exact m22Stab5_fix4 g
    · exact m22Stab5_fix14 g
  · exact hx

public theorem m22Stab5_maps_pair916 (g : m22Stab5) {x : Fin 22}
    (hx : x ∈ m22Pair916) : m22Stab5Perm g x ∈ m22Pair916 := by
  rw [← show m22Hexad24Ten \ {2, 4, 10, 14} = m22Pair916 by decide +kernel] at hx ⊢
  apply image_mem_sdiff_of_fixed (m22Stab5Perm g) m22Hexad24Ten {2, 4, 10, 14}
  · exact m22Stab5_smul_hexad24Ten g
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact m22Stab5_fix2 g
    · exact m22Stab5_fix4 g
    · exact m22Stab5_fix10 g
    · exact m22Stab5_fix14 g
  · exact hx

public theorem m22Stab5_maps_pair1217 (g : m22Stab5) {x : Fin 22}
    (hx : x ∈ m22Pair1217) : m22Stab5Perm g x ∈ m22Pair1217 := by
  rw [← show m22Hexad14Ten \ {1, 4, 6, 10} = m22Pair1217 by decide +kernel] at hx ⊢
  apply image_mem_sdiff_of_fixed (m22Stab5Perm g) m22Hexad14Ten {1, 4, 6, 10}
  · exact m22Stab5_smul_hexad14Ten g
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact m22Stab5_fix1 g
    · exact m22Stab5_fix4 g
    · exact m22Stab5_fix6 g
    · exact m22Stab5_fix10 g
  · exact hx

public theorem m22Stab5_maps_pair1521 (g : m22Stab5) {x : Fin 22}
    (hx : x ∈ m22Pair1521) : m22Stab5Perm g x ∈ m22Pair1521 := by
  rw [← show m22Hexad124 \ {1, 2, 4, 7} = m22Pair1521 by decide +kernel] at hx ⊢
  apply image_mem_sdiff_of_fixed (m22Stab5Perm g) m22Hexad124 {1, 2, 4, 7}
  · exact m22Stab5_smul_hexad124 g
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact m22Stab5_fix1 g
    · exact m22Stab5_fix2 g
    · exact m22Stab5_fix4 g
    · exact m22Stab5_fix7 g
  · exact hx

public theorem m22Stab5_maps_pair1820 (g : m22Stab5) {x : Fin 22}
    (hx : x ∈ m22Pair1820) : m22Stab5Perm g x ∈ m22Pair1820 := by
  rw [← show m22Hexad123 \ {1, 2, 3, 10} = m22Pair1820 by decide +kernel] at hx ⊢
  apply image_mem_sdiff_of_fixed (m22Stab5Perm g) m22Hexad123 {1, 2, 3, 10}
  · exact m22Stab5_smul_hexad123 g
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact m22Stab5_fix1 g
    · exact m22Stab5_fix2 g
    · exact m22Stab5_fix3 g
    · exact m22Stab5_fix10 g
  · exact hx

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

public theorem m22Stab5_image_mem
    (g : m22Stab5) (i : Fin 77) {x : Fin 22}
    (hx : x ∈ m22BlockAt i) :
    m22Stab5Perm g x ∈ m22Stab5Perm g • m22BlockAt i :=
  Finset.smul_mem_smul_finset (a := m22Stab5Perm g) hx

/-- Identify the image of an indexed hexad from the images of three of its points. -/
public theorem m22Stab5_smul_block_eq_of_maps_triple
    (g : m22Stab5) (i j : Fin 77)
    (x₁ x₂ x₃ y₁ y₂ y₃ : Fin 22)
    (hCard : ({y₁, y₂, y₃} : Finset (Fin 22)).card = 3)
    (hSource : ({x₁, x₂, x₃} : Finset (Fin 22)) ⊆ m22BlockAt i)
    (hTarget : ({y₁, y₂, y₃} : Finset (Fin 22)) ⊆ m22BlockAt j)
    (h₁ : m22Stab5Perm g x₁ = y₁)
    (h₂ : m22Stab5Perm g x₂ = y₂)
    (h₃ : m22Stab5Perm g x₃ = y₃) :
    m22Stab5Perm g • m22BlockAt i = m22BlockAt j := by
  apply m22Blocks_eq_of_common_triple
    {y₁, y₂, y₃} (m22Stab5Perm g • m22BlockAt i) (m22BlockAt j)
  · exact hCard
  · exact m22_smul_block_mem (m22Stab5M22 g) (m22BlockAt i) (m22BlockAt_mem i)
  · exact m22BlockAt_mem j
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simpa [h₁] using m22Stab5_image_mem g i (x := x₁)
        (hSource (by simp))
    · simpa [h₂] using m22Stab5_image_mem g i (x := x₂)
        (hSource (by simp))
    · simpa [h₃] using m22Stab5_image_mem g i (x := x₃)
        (hSource (by simp))
  · exact hTarget

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

/-- The block through points 1 and 2 linking the pair variables
`011`, `813`, `916`, and `1217` forces their orientations to agree. -/
public theorem m22Stab5_constraint12 (g : m22Stab5) :
    (m22Stab5Perm g 0 = 0 ∧ m22Stab5Perm g 8 = 8 ∧
      m22Stab5Perm g 9 = 9 ∧ m22Stab5Perm g 17 = 17) ∨
    (m22Stab5Perm g 0 = 11 ∧ m22Stab5Perm g 8 = 13 ∧
      m22Stab5Perm g 9 = 16 ∧ m22Stab5Perm g 17 = 12) := by
  have h0Pair := m22Stab5_maps_pair011 g (x := (0 : Fin 22)) (by decide +kernel)
  have h8Pair := m22Stab5_maps_pair813 g (x := (8 : Fin 22)) (by decide +kernel)
  have h9Pair := m22Stab5_maps_pair916 g (x := (9 : Fin 22)) (by decide +kernel)
  have h17Pair := m22Stab5_maps_pair1217 g (x := (17 : Fin 22)) (by decide +kernel)
  have h0Cases :
      m22Stab5Perm g 0 = 0 ∨ m22Stab5Perm g 0 = 11 := by
    simpa [m22Pair011] using h0Pair
  rcases h0Cases with h0 | h0
  · left
    have hImageEq :
        m22Stab5Perm g • m22BlockAt 3 = m22BlockAt 3 :=
      m22Stab5_smul_block_eq_of_maps_triple
        g 3 3 0 1 2 0 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        h0 (m22Stab5_fix1 g) (m22Stab5_fix2 g)
    have h8Block : m22Stab5Perm g 8 ∈ m22BlockAt 3 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 3 (by decide +kernel)
    have h9Block : m22Stab5Perm g 9 ∈ m22BlockAt 3 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 3 (by decide +kernel)
    have h17Block : m22Stab5Perm g 17 ∈ m22BlockAt 3 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 3 (by decide +kernel)
    refine ⟨h0, ?_, ?_, ?_⟩
    · rcases (show m22Stab5Perm g 8 = 8 ∨ m22Stab5Perm g 8 = 13 by
        simpa [m22Pair813] using h8Pair) with h8 | h8
      · exact h8
      · exfalso
        have h8bad : ¬ (13 ∈ m22BlockAt 3) := by decide +kernel
        have h8mem : 13 ∈ m22BlockAt 3 := by simpa [h8] using h8Block
        exact h8bad h8mem
    · rcases (show m22Stab5Perm g 9 = 9 ∨ m22Stab5Perm g 9 = 16 by
        simpa [m22Pair916] using h9Pair) with h9 | h9
      · exact h9
      · exfalso
        have h9bad : ¬ (16 ∈ m22BlockAt 3) := by decide +kernel
        have h9mem : 16 ∈ m22BlockAt 3 := by simpa [h9] using h9Block
        exact h9bad h9mem
    · rcases (show m22Stab5Perm g 17 = 12 ∨ m22Stab5Perm g 17 = 17 by
        simpa [m22Pair1217] using h17Pair) with h17 | h17
      · exfalso
        have h17bad : ¬ (12 ∈ m22BlockAt 3) := by decide +kernel
        have h17mem : 12 ∈ m22BlockAt 3 := by simpa [h17] using h17Block
        exact h17bad h17mem
      · exact h17
  · right
    have hImageEq :
        m22Stab5Perm g • m22BlockAt 3 = m22BlockAt 4 :=
      m22Stab5_smul_block_eq_of_maps_triple
        g 3 4 0 1 2 11 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        h0 (m22Stab5_fix1 g) (m22Stab5_fix2 g)
    have h8Block : m22Stab5Perm g 8 ∈ m22BlockAt 4 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 3 (by decide +kernel)
    have h9Block : m22Stab5Perm g 9 ∈ m22BlockAt 4 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 3 (by decide +kernel)
    have h17Block : m22Stab5Perm g 17 ∈ m22BlockAt 4 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 3 (by decide +kernel)
    refine ⟨h0, ?_, ?_, ?_⟩
    · rcases (show m22Stab5Perm g 8 = 8 ∨ m22Stab5Perm g 8 = 13 by
        simpa [m22Pair813] using h8Pair) with h8 | h8
      · exfalso
        have h8bad : ¬ (8 ∈ m22BlockAt 4) := by decide +kernel
        have h8mem : 8 ∈ m22BlockAt 4 := by simpa [h8] using h8Block
        exact h8bad h8mem
      · exact h8
    · rcases (show m22Stab5Perm g 9 = 9 ∨ m22Stab5Perm g 9 = 16 by
        simpa [m22Pair916] using h9Pair) with h9 | h9
      · exfalso
        have h9bad : ¬ (9 ∈ m22BlockAt 4) := by decide +kernel
        have h9mem : 9 ∈ m22BlockAt 4 := by simpa [h9] using h9Block
        exact h9bad h9mem
      · exact h9
    · rcases (show m22Stab5Perm g 17 = 12 ∨ m22Stab5Perm g 17 = 17 by
        simpa [m22Pair1217] using h17Pair) with h17 | h17
      · exact h17
      · exfalso
        have h17bad : ¬ (17 ∈ m22BlockAt 4) := by decide +kernel
        have h17mem : 17 ∈ m22BlockAt 4 := by simpa [h17] using h17Block
        exact h17bad h17mem

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

/-- The block through points 1 and 3 linking the pair variables
`011`, `519`, `1217`, and `1521` forces their orientations to agree. -/
public theorem m22Stab5_constraint13 (g : m22Stab5) :
    (m22Stab5Perm g 0 = 0 ∧ m22Stab5Perm g 5 = 5 ∧
      m22Stab5Perm g 12 = 12 ∧ m22Stab5Perm g 21 = 21) ∨
    (m22Stab5Perm g 0 = 11 ∧ m22Stab5Perm g 5 = 19 ∧
      m22Stab5Perm g 12 = 17 ∧ m22Stab5Perm g 21 = 15) := by
  have h0Pair := m22Stab5_maps_pair011 g (x := (0 : Fin 22)) (by decide +kernel)
  have h5Pair := m22Stab5_maps_pair519 g (x := (5 : Fin 22)) (by decide +kernel)
  have h12Pair := m22Stab5_maps_pair1217 g (x := (12 : Fin 22)) (by decide +kernel)
  have h21Pair := m22Stab5_maps_pair1521 g (x := (21 : Fin 22)) (by decide +kernel)
  have h0Cases :
      m22Stab5Perm g 0 = 0 ∨ m22Stab5Perm g 0 = 11 := by
    simpa [m22Pair011] using h0Pair
  rcases h0Cases with h0 | h0
  · left
    have hImageEq :
        m22Stab5Perm g • m22BlockAt 6 = m22BlockAt 6 :=
      m22Stab5_smul_block_eq_of_maps_triple
        g 6 6 0 1 3 0 1 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        h0 (m22Stab5_fix1 g) (m22Stab5_fix3 g)
    have h5Block : m22Stab5Perm g 5 ∈ m22BlockAt 6 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 6 (by decide +kernel)
    have h12Block : m22Stab5Perm g 12 ∈ m22BlockAt 6 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 6 (by decide +kernel)
    have h21Block : m22Stab5Perm g 21 ∈ m22BlockAt 6 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 6 (by decide +kernel)
    refine ⟨h0, ?_, ?_, ?_⟩
    · rcases (show m22Stab5Perm g 5 = 5 ∨ m22Stab5Perm g 5 = 19 by
        simpa [m22Pair519] using h5Pair) with h5 | h5
      · exact h5
      · exfalso
        have h5bad : ¬ (19 ∈ m22BlockAt 6) := by decide +kernel
        have h5mem : 19 ∈ m22BlockAt 6 := by simpa [h5] using h5Block
        exact h5bad h5mem
    · rcases (show m22Stab5Perm g 12 = 12 ∨ m22Stab5Perm g 12 = 17 by
        simpa [m22Pair1217] using h12Pair) with h12 | h12
      · exact h12
      · exfalso
        have h12bad : ¬ (17 ∈ m22BlockAt 6) := by decide +kernel
        have h12mem : 17 ∈ m22BlockAt 6 := by simpa [h12] using h12Block
        exact h12bad h12mem
    · rcases (show m22Stab5Perm g 21 = 15 ∨ m22Stab5Perm g 21 = 21 by
        simpa [m22Pair1521] using h21Pair) with h21 | h21
      · exfalso
        have h21bad : ¬ (15 ∈ m22BlockAt 6) := by decide +kernel
        have h21mem : 15 ∈ m22BlockAt 6 := by simpa [h21] using h21Block
        exact h21bad h21mem
      · exact h21
  · right
    have hImageEq :
        m22Stab5Perm g • m22BlockAt 6 = m22BlockAt 8 :=
      m22Stab5_smul_block_eq_of_maps_triple
        g 6 8 0 1 3 11 1 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        h0 (m22Stab5_fix1 g) (m22Stab5_fix3 g)
    have h5Block : m22Stab5Perm g 5 ∈ m22BlockAt 8 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 6 (by decide +kernel)
    have h12Block : m22Stab5Perm g 12 ∈ m22BlockAt 8 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 6 (by decide +kernel)
    have h21Block : m22Stab5Perm g 21 ∈ m22BlockAt 8 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 6 (by decide +kernel)
    refine ⟨h0, ?_, ?_, ?_⟩
    · rcases (show m22Stab5Perm g 5 = 5 ∨ m22Stab5Perm g 5 = 19 by
        simpa [m22Pair519] using h5Pair) with h5 | h5
      · exfalso
        have h5bad : ¬ (5 ∈ m22BlockAt 8) := by decide +kernel
        have h5mem : 5 ∈ m22BlockAt 8 := by simpa [h5] using h5Block
        exact h5bad h5mem
      · exact h5
    · rcases (show m22Stab5Perm g 12 = 12 ∨ m22Stab5Perm g 12 = 17 by
        simpa [m22Pair1217] using h12Pair) with h12 | h12
      · exfalso
        have h12bad : ¬ (12 ∈ m22BlockAt 8) := by decide +kernel
        have h12mem : 12 ∈ m22BlockAt 8 := by simpa [h12] using h12Block
        exact h12bad h12mem
      · exact h12
    · rcases (show m22Stab5Perm g 21 = 15 ∨ m22Stab5Perm g 21 = 21 by
        simpa [m22Pair1521] using h21Pair) with h21 | h21
      · exact h21
      · exfalso
        have h21bad : ¬ (21 ∈ m22BlockAt 8) := by decide +kernel
        have h21mem : 21 ∈ m22BlockAt 8 := by simpa [h21] using h21Block
        exact h21bad h21mem

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

/-- The block through points 1 and 4 linking the pair variables
`519`, `916`, `011`, and `1820` forces their orientations to agree. -/
public theorem m22Stab5_constraint14 (g : m22Stab5) :
    (m22Stab5Perm g 5 = 5 ∧ m22Stab5Perm g 9 = 9 ∧
      m22Stab5Perm g 11 = 11 ∧ m22Stab5Perm g 18 = 18) ∨
    (m22Stab5Perm g 5 = 19 ∧ m22Stab5Perm g 9 = 16 ∧
      m22Stab5Perm g 11 = 0 ∧ m22Stab5Perm g 18 = 20) := by
  have h5Pair := m22Stab5_maps_pair519 g (x := (5 : Fin 22)) (by decide +kernel)
  have h9Pair := m22Stab5_maps_pair916 g (x := (9 : Fin 22)) (by decide +kernel)
  have h11Pair := m22Stab5_maps_pair011 g (x := (11 : Fin 22)) (by decide +kernel)
  have h18Pair := m22Stab5_maps_pair1820 g (x := (18 : Fin 22)) (by decide +kernel)
  have h5Cases :
      m22Stab5Perm g 5 = 5 ∨ m22Stab5Perm g 5 = 19 := by
    simpa [m22Pair519] using h5Pair
  rcases h5Cases with h5 | h5
  · left
    have hImageEq :
        m22Stab5Perm g • m22BlockAt 9 = m22BlockAt 9 :=
      m22Stab5_smul_block_eq_of_maps_triple
        g 9 9 5 1 4 5 1 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        h5 (m22Stab5_fix1 g) (m22Stab5_fix4 g)
    have h9Block : m22Stab5Perm g 9 ∈ m22BlockAt 9 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 9 (by decide +kernel)
    have h11Block : m22Stab5Perm g 11 ∈ m22BlockAt 9 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 9 (by decide +kernel)
    have h18Block : m22Stab5Perm g 18 ∈ m22BlockAt 9 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 9 (by decide +kernel)
    refine ⟨h5, ?_, ?_, ?_⟩
    · rcases (show m22Stab5Perm g 9 = 9 ∨ m22Stab5Perm g 9 = 16 by
        simpa [m22Pair916] using h9Pair) with h9 | h9
      · exact h9
      · exfalso
        have h9bad : ¬ (16 ∈ m22BlockAt 9) := by decide +kernel
        have h9mem : 16 ∈ m22BlockAt 9 := by simpa [h9] using h9Block
        exact h9bad h9mem
    · rcases (show m22Stab5Perm g 11 = 0 ∨ m22Stab5Perm g 11 = 11 by
        simpa [m22Pair011] using h11Pair) with h11 | h11
      · exfalso
        have h11bad : ¬ (0 ∈ m22BlockAt 9) := by decide +kernel
        have h11mem : 0 ∈ m22BlockAt 9 := by simpa [h11] using h11Block
        exact h11bad h11mem
      · exact h11
    · rcases (show m22Stab5Perm g 18 = 18 ∨ m22Stab5Perm g 18 = 20 by
        simpa [m22Pair1820] using h18Pair) with h18 | h18
      · exact h18
      · exfalso
        have h18bad : ¬ (20 ∈ m22BlockAt 9) := by decide +kernel
        have h18mem : 20 ∈ m22BlockAt 9 := by simpa [h18] using h18Block
        exact h18bad h18mem
  · right
    have hImageEq :
        m22Stab5Perm g • m22BlockAt 9 = m22BlockAt 11 :=
      m22Stab5_smul_block_eq_of_maps_triple
        g 9 11 5 1 4 19 1 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        h5 (m22Stab5_fix1 g) (m22Stab5_fix4 g)
    have h9Block : m22Stab5Perm g 9 ∈ m22BlockAt 11 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 9 (by decide +kernel)
    have h11Block : m22Stab5Perm g 11 ∈ m22BlockAt 11 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 9 (by decide +kernel)
    have h18Block : m22Stab5Perm g 18 ∈ m22BlockAt 11 := by
      rw [← hImageEq]
      exact m22Stab5_image_mem g 9 (by decide +kernel)
    refine ⟨h5, ?_, ?_, ?_⟩
    · rcases (show m22Stab5Perm g 9 = 9 ∨ m22Stab5Perm g 9 = 16 by
        simpa [m22Pair916] using h9Pair) with h9 | h9
      · exfalso
        have h9bad : ¬ (9 ∈ m22BlockAt 11) := by decide +kernel
        have h9mem : 9 ∈ m22BlockAt 11 := by simpa [h9] using h9Block
        exact h9bad h9mem
      · exact h9
    · rcases (show m22Stab5Perm g 11 = 0 ∨ m22Stab5Perm g 11 = 11 by
        simpa [m22Pair011] using h11Pair) with h11 | h11
      · exact h11
      · exfalso
        have h11bad : ¬ (11 ∈ m22BlockAt 11) := by decide +kernel
        have h11mem : 11 ∈ m22BlockAt 11 := by simpa [h11] using h11Block
        exact h11bad h11mem
    · rcases (show m22Stab5Perm g 18 = 18 ∨ m22Stab5Perm g 18 = 20 by
        simpa [m22Pair1820] using h18Pair) with h18 | h18
      · exfalso
        have h18bad : ¬ (18 ∈ m22BlockAt 11) := by decide +kernel
        have h18mem : 18 ∈ m22BlockAt 11 := by simpa [h18] using h18Block
        exact h18bad h18mem
      · exact h18

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- The unique nontrivial permutation compatible with all seven pair blocks
before imposing evenness. -/
@[expose] public def m22OddPairSwap : Equiv.Perm (Fin 22) :=
  Equiv.swap 0 11 * Equiv.swap 5 19 * Equiv.swap 8 13 *
    Equiv.swap 9 16 * Equiv.swap 12 17 * Equiv.swap 15 21 *
    Equiv.swap 18 20

/-- The simultaneous swap of the seven residual pairs is odd. -/
public theorem m22OddPairSwap_not_alternating :
    m22OddPairSwap ∉ alternatingGroup (Fin 22) := by
  intro h
  rw [Equiv.Perm.mem_alternatingGroup] at h
  simp [m22OddPairSwap, Equiv.Perm.sign_swap'] at h

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


public theorem perm_fix_other_of_pair {α : Type*}
    (p : Equiv.Perm α) {a b : α} (hab : a ≠ b)
    (ha : p a = a) (hb : p b = a ∨ p b = b) : p b = b := by
  rcases hb with hb | hb
  · exact (hab (p.injective (ha.trans hb.symm))).elim
  · exact hb

public theorem perm_swap_other_of_pair {α : Type*}
    (p : Equiv.Perm α) {a b : α} (hab : a ≠ b)
    (ha : p a = b) (hb : p b = a ∨ p b = b) : p b = a := by
  rcases hb with hb | hb
  · exact hb
  · exact (hab (p.injective (ha.trans hb.symm))).elim

public theorem m22Stab5Perm_injective :
    Function.Injective m22Stab5Perm := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hgh

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- A five-point stabilizer element fixing point 0 fixes all 22 points. -/
public theorem m22Stab5_eq_one_of_fix0
    (g : m22Stab5) (h0 : m22Stab5Perm g 0 = 0) : g = 1 := by
  have h0ne11 : (0 : Fin 22) ≠ 11 := by decide +kernel
  have h5ne19 : (5 : Fin 22) ≠ 19 := by decide +kernel
  have h12 :
      m22Stab5Perm g 0 = 0 ∧ m22Stab5Perm g 8 = 8 ∧
        m22Stab5Perm g 9 = 9 ∧ m22Stab5Perm g 17 = 17 := by
    rcases m22Stab5_constraint12 g with h12 | h12
    · exact h12
    · exact (h0ne11 (h0.symm.trans h12.1)).elim
  have h13 :
      m22Stab5Perm g 0 = 0 ∧ m22Stab5Perm g 5 = 5 ∧
        m22Stab5Perm g 12 = 12 ∧ m22Stab5Perm g 21 = 21 := by
    rcases m22Stab5_constraint13 g with h13 | h13
    · exact h13
    · exact (h0ne11 (h0.symm.trans h13.1)).elim
  have h14 :
      m22Stab5Perm g 5 = 5 ∧ m22Stab5Perm g 9 = 9 ∧
        m22Stab5Perm g 11 = 11 ∧ m22Stab5Perm g 18 = 18 := by
    rcases m22Stab5_constraint14 g with h14 | h14
    · exact h14
    · exact (h5ne19 (h13.2.1.symm.trans h14.1)).elim
  have h19Cases :
      m22Stab5Perm g 19 = 5 ∨ m22Stab5Perm g 19 = 19 := by
    simpa [m22Pair519] using
      m22Stab5_maps_pair519 g (x := (19 : Fin 22)) (by decide +kernel)
  have h13Cases :
      m22Stab5Perm g 13 = 8 ∨ m22Stab5Perm g 13 = 13 := by
    simpa [m22Pair813] using
      m22Stab5_maps_pair813 g (x := (13 : Fin 22)) (by decide +kernel)
  have h16Cases :
      m22Stab5Perm g 16 = 9 ∨ m22Stab5Perm g 16 = 16 := by
    simpa [m22Pair916] using
      m22Stab5_maps_pair916 g (x := (16 : Fin 22)) (by decide +kernel)
  have h15Cases :
      m22Stab5Perm g 15 = 21 ∨ m22Stab5Perm g 15 = 15 := by
    have h :
        m22Stab5Perm g 15 = 15 ∨ m22Stab5Perm g 15 = 21 := by
      simpa [m22Pair1521] using
        m22Stab5_maps_pair1521 g (x := (15 : Fin 22)) (by decide +kernel)
    exact h.elim Or.inr Or.inl
  have h20Cases :
      m22Stab5Perm g 20 = 18 ∨ m22Stab5Perm g 20 = 20 := by
    simpa [m22Pair1820] using
      m22Stab5_maps_pair1820 g (x := (20 : Fin 22)) (by decide +kernel)
  have h19 : m22Stab5Perm g 19 = 19 :=
    perm_fix_other_of_pair (m22Stab5Perm g) (by decide +kernel) h13.2.1 h19Cases
  have h13' : m22Stab5Perm g 13 = 13 :=
    perm_fix_other_of_pair (m22Stab5Perm g) (by decide +kernel) h12.2.1 h13Cases
  have h16 : m22Stab5Perm g 16 = 16 :=
    perm_fix_other_of_pair (m22Stab5Perm g) (by decide +kernel) h12.2.2.1 h16Cases
  have h15 : m22Stab5Perm g 15 = 15 :=
    perm_fix_other_of_pair (m22Stab5Perm g) (by decide +kernel) h13.2.2.2 h15Cases
  have h20 : m22Stab5Perm g 20 = 20 :=
    perm_fix_other_of_pair (m22Stab5Perm g) (by decide +kernel) h14.2.2.2 h20Cases
  have hPerm : m22Stab5Perm g = 1 := by
    ext x
    fin_cases x <;>
      simp [h12.1, h12.2.1, h12.2.2.1, h12.2.2.2,
        h13.2.1, h13.2.2.1, h13.2.2.2,
        h14.2.2.1, h14.2.2.2, h19, h13', h16, h15, h20,
        m22Stab5_fix1 g, m22Stab5_fix2 g, m22Stab5_fix3 g,
        m22Stab5_fix4 g, m22Stab5_fix6 g, m22Stab5_fix7 g,
        m22Stab5_fix10 g, m22Stab5_fix14 g]
  apply m22Stab5Perm_injective
  simpa using hPerm

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- No element of the even Steiner group can exchange point 0 with point 11
while fixing the five base points. -/
public theorem m22Stab5_not_map0_to11
    (g : m22Stab5) (h0 : m22Stab5Perm g 0 = 11) : False := by
  have h0ne11 : (0 : Fin 22) ≠ 11 := by decide +kernel
  have h5ne19 : (5 : Fin 22) ≠ 19 := by decide +kernel
  have h12 :
      m22Stab5Perm g 0 = 11 ∧ m22Stab5Perm g 8 = 13 ∧
        m22Stab5Perm g 9 = 16 ∧ m22Stab5Perm g 17 = 12 := by
    rcases m22Stab5_constraint12 g with h12 | h12
    · exact (h0ne11 (h12.1.symm.trans h0)).elim
    · exact h12
  have h13 :
      m22Stab5Perm g 0 = 11 ∧ m22Stab5Perm g 5 = 19 ∧
        m22Stab5Perm g 12 = 17 ∧ m22Stab5Perm g 21 = 15 := by
    rcases m22Stab5_constraint13 g with h13 | h13
    · exact (h0ne11 (h13.1.symm.trans h0)).elim
    · exact h13
  have h14 :
      m22Stab5Perm g 5 = 19 ∧ m22Stab5Perm g 9 = 16 ∧
        m22Stab5Perm g 11 = 0 ∧ m22Stab5Perm g 18 = 20 := by
    rcases m22Stab5_constraint14 g with h14 | h14
    · exact (h5ne19 (h14.1.symm.trans h13.2.1)).elim
    · exact h14
  have h19Cases :
      m22Stab5Perm g 19 = 5 ∨ m22Stab5Perm g 19 = 19 := by
    simpa [m22Pair519] using
      m22Stab5_maps_pair519 g (x := (19 : Fin 22)) (by decide +kernel)
  have h13Cases :
      m22Stab5Perm g 13 = 8 ∨ m22Stab5Perm g 13 = 13 := by
    simpa [m22Pair813] using
      m22Stab5_maps_pair813 g (x := (13 : Fin 22)) (by decide +kernel)
  have h16Cases :
      m22Stab5Perm g 16 = 9 ∨ m22Stab5Perm g 16 = 16 := by
    simpa [m22Pair916] using
      m22Stab5_maps_pair916 g (x := (16 : Fin 22)) (by decide +kernel)
  have h15Cases :
      m22Stab5Perm g 15 = 21 ∨ m22Stab5Perm g 15 = 15 := by
    have h :
        m22Stab5Perm g 15 = 15 ∨ m22Stab5Perm g 15 = 21 := by
      simpa [m22Pair1521] using
        m22Stab5_maps_pair1521 g (x := (15 : Fin 22)) (by decide +kernel)
    exact h.elim Or.inr Or.inl
  have h20Cases :
      m22Stab5Perm g 20 = 18 ∨ m22Stab5Perm g 20 = 20 := by
    simpa [m22Pair1820] using
      m22Stab5_maps_pair1820 g (x := (20 : Fin 22)) (by decide +kernel)
  have h19 : m22Stab5Perm g 19 = 5 :=
    perm_swap_other_of_pair (m22Stab5Perm g) (by decide +kernel) h13.2.1 h19Cases
  have h13' : m22Stab5Perm g 13 = 8 :=
    perm_swap_other_of_pair (m22Stab5Perm g) (by decide +kernel) h12.2.1 h13Cases
  have h16 : m22Stab5Perm g 16 = 9 :=
    perm_swap_other_of_pair (m22Stab5Perm g) (by decide +kernel) h12.2.2.1 h16Cases
  have h15 : m22Stab5Perm g 15 = 21 :=
    perm_swap_other_of_pair (m22Stab5Perm g) (by decide +kernel) h13.2.2.2 h15Cases
  have h20 : m22Stab5Perm g 20 = 18 :=
    perm_swap_other_of_pair (m22Stab5Perm g) (by decide +kernel) h14.2.2.2 h20Cases
  have hPerm : m22Stab5Perm g = m22OddPairSwap := by
    ext x
    fin_cases x <;>
      simp [m22OddPairSwap, Equiv.swap_apply_def, h12.1, h12.2.1, h12.2.2.1, h12.2.2.2,
        h13.2.1, h13.2.2.1, h13.2.2.2,
        h14.2.2.1, h14.2.2.2, h19, h13', h16, h15, h20,
        m22Stab5_fix1 g, m22Stab5_fix2 g, m22Stab5_fix3 g,
        m22Stab5_fix4 g, m22Stab5_fix6 g, m22Stab5_fix7 g,
        m22Stab5_fix10 g, m22Stab5_fix14 g]
  have hAlt : m22Stab5Perm g ∈ alternatingGroup (Fin 22) :=
    M22_le_alternatingGroup (m22Stab5M22 g).property
  rw [hPerm] at hAlt
  exact m22OddPairSwap_not_alternating hAlt

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- The five-point stabilizer in the Steiner-defined M22 is trivial. -/
public theorem m22Stab5_eq_one (g : m22Stab5) : g = 1 := by
  have h0Pair := m22Stab5_maps_pair011 g (x := (0 : Fin 22)) (by decide +kernel)
  have h0Cases :
      m22Stab5Perm g 0 = 0 ∨ m22Stab5Perm g 0 = 11 := by
    simpa [m22Pair011] using h0Pair
  rcases h0Cases with h0 | h0
  · exact m22Stab5_eq_one_of_fix0 g h0
  · exact (m22Stab5_not_map0_to11 g h0).elim

/-- The terminal stabilizer contributes no further orbit--stabilizer factor. -/
public theorem m22Stab5_card : Nat.card m22Stab5 = 1 :=
  Nat.card_eq_one_iff_exists.mpr ⟨1, fun g => m22Stab5_eq_one g⟩

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- Orbit--stabilizer upper bound for the standard even Steiner definition of M22. -/
public theorem m22_order_upper_bound : Nat.card M22 ≤ 443520 := by
  calc
    Nat.card M22 ≤ 22 * Nat.card m22Stab1 :=
      m22_card_le_22_mul_stab1
    _ ≤ 22 * (21 * Nat.card m22Stab2) :=
      Nat.mul_le_mul_left 22 m22_stab1_card_le_21_mul_stab2
    _ ≤ 22 * (21 * (20 * Nat.card m22Stab3)) :=
      Nat.mul_le_mul_left 22
        (Nat.mul_le_mul_left 21 m22_stab2_card_le_20_mul_stab3)
    _ ≤ 22 * (21 * (20 * (16 * Nat.card m22Stab4))) :=
      Nat.mul_le_mul_left 22
        (Nat.mul_le_mul_left 21
          (Nat.mul_le_mul_left 20 m22_stab3_card_le_16_mul_stab4))
    _ ≤ 22 * (21 * (20 * (16 * (3 * Nat.card m22Stab5)))) :=
      Nat.mul_le_mul_left 22
        (Nat.mul_le_mul_left 21
          (Nat.mul_le_mul_left 20
            (Nat.mul_le_mul_left 16 m22_stab4_card_le_3_mul_stab5)))
    _ = 443520 := by rw [m22Stab5_card]

end Sporadic.Mathieu
