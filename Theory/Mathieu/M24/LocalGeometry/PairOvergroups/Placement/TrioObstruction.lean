module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TrioObstruction.Generators
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# An elementary nine-subgroup that preserves no octad trio

The two certified permutations generate an elementary abelian subgroup of
order nine. Both fix point 1, and their joint orbit of point 6 has nine
points. If they preserved a trio, the part containing 1 would be fixed.
An order-three permutation of three parts with a fixed part is trivial, so
both generators would fix each part. The nine-point orbit could then fit
inside an eight-point octad, a contradiction.

This proves an unconditional obstruction in the fixed Witt-design carrier,
including for every translate of the standard trio. It does not prove the
existence of a Sylow subgroup permuting with the elementary nine-subgroup.
The separate `source/check_pair.g` reproduces the computational evidence for
that additional fact; its assertions are not used as Lean proofs.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528); Aschbacher, *Sporadic Groups*, Chapter 7, §20. The source's
irreducibility sieve must not be replaced by an unsupported universal trio
placement for every `PairInput`.
-/

@[expose] public section

open scoped Pointwise
open Subgroup

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TrioObstruction

set_option maxRecDepth 100000

private theorem part_fixed (T : Trio) (g : Equiv.Perm (Fin 24))
    (hg : ∀ A ∈ T.parts, g • A ∈ T.parts) (hpow : g ^ 3 = 1)
    (hfix : g 1 = 1) {A : Finset (Fin 24)} (hA : A ∈ T.parts) : g • A = A := by
  classical
  have hcover : (1 : Fin 24) ∈ T.parts.biUnion id := by rw [T.cover]; simp
  obtain ⟨B, hB, h1B⟩ := Finset.mem_biUnion.mp hcover
  have hBg : g • B = B := by
    by_contra hne
    have hd := T.disjoint (g • B) (hg B hB) B hB hne
    have hm : (1 : Fin 24) ∈ g • B := by
      simpa only [id_eq, Equiv.Perm.smul_def, hfix] using Finset.smul_mem_smul_finset (a := g) h1B
    exact Finset.disjoint_left.mp hd hm h1B
  by_contra hn
  have hc : g • (g • (g • A)) = A := by
    calc
      g • (g • (g • A)) = (g ^ 3) • A := by simp [pow_succ, mul_smul]
      _ = A := by rw [hpow, one_smul]
  have hAB : A ≠ B := by rintro rfl; exact hn hBg
  have hUA : g • A ≠ A := hn
  have hVA : g • (g • A) ≠ A := by
    intro he
    have he' := congrArg (fun C : Finset (Fin 24) => g • C) he
    rw [hc] at he'
    exact hn he'.symm
  have hVU : g • (g • A) ≠ g • A := by
    intro he
    exact hn (smul_left_cancel g he)
  have hUB : g • A ≠ B := by
    intro he
    exact hAB (smul_left_cancel g (he.trans hBg.symm))
  have hVB : g • (g • A) ≠ B := by
    intro he
    exact hUB (smul_left_cancel g (he.trans hBg.symm))
  have hs : {B, A, g • A, g • (g • A)} ⊆ T.parts := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · exact hB
    · exact hA
    · exact hg A hA
    · exact hg _ (hg A hA)
  have hcard := Finset.card_le_card hs
  have hfour : ({B, A, g • A, g • (g • A)} : Finset (Finset (Fin 24))).card = 4 := by
    have hB0 : B ∉ ({A, g • A, g • (g • A)} : Finset (Finset (Fin 24))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hAB, Ne.symm hUB, Ne.symm hVB⟩
    have hA0 : A ∉ ({g • A, g • (g • A)} : Finset (Finset (Fin 24))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hUA, Ne.symm hVA⟩
    have hU0 : g • A ∉ ({g • (g • A)} : Finset (Finset (Fin 24))) := by
      simpa only [Finset.mem_singleton] using Ne.symm hVU
    rw [Finset.card_insert_of_notMem hB0, Finset.card_insert_of_notMem hA0,
      Finset.card_insert_of_notMem hU0, Finset.card_singleton]
  rw [hfour, T.card] at hcard
  omega

private def nineOrbit : Finset (Fin 24) :=
  Finset.univ.image fun ij : Fin 3 × Fin 3 =>
    (xPerm ^ ij.1.val * yPerm ^ ij.2.val) 6

private theorem nineOrbit_card : nineOrbit.card = 9 := by decide +kernel

private theorem no_trio (T : Trio)
    (hx : ∀ A ∈ T.parts, xPerm • A ∈ T.parts)
    (hy : ∀ A ∈ T.parts, yPerm • A ∈ T.parts) : False := by
  classical
  have hcover : (6 : Fin 24) ∈ T.parts.biUnion id := by rw [T.cover]; simp
  obtain ⟨A, hA, h6A⟩ := Finset.mem_biUnion.mp hcover
  have hX : xPerm ∈ MulAction.stabilizer (Equiv.Perm (Fin 24)) A :=
    part_fixed T xPerm hx (by decide +kernel) (by decide +kernel) hA
  have hY : yPerm ∈ MulAction.stabilizer (Equiv.Perm (Fin 24)) A :=
    part_fixed T yPerm hy (by decide +kernel) (by decide +kernel) hA
  have hsub : nineOrbit ⊆ A := by
    intro a ha
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp ha
    have he := (MulAction.stabilizer (Equiv.Perm (Fin 24)) A).mul_mem
      ((MulAction.stabilizer (Equiv.Perm (Fin 24)) A).pow_mem hX ij.1.val)
      ((MulAction.stabilizer (Equiv.Perm (Fin 24)) A).pow_mem hY ij.2.val)
    have hm := Finset.smul_mem_smul_finset
      (a := xPerm ^ ij.1.val * yPerm ^ ij.2.val) h6A
    change (xPerm ^ ij.1.val * yPerm ^ ij.2.val) 6 ∈
      (xPerm ^ ij.1.val * yPerm ^ ij.2.val) • A at hm
    rwa [show (xPerm ^ ij.1.val * yPerm ^ ij.2.val) • A = A from he] at hm
  have hcard := Finset.card_le_card hsub
  rw [nineOrbit_card, T.part_card hA] at hcard
  omega

private theorem x_order : orderOf x = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have hne : (x : Equiv.Perm (Fin 24)) ≠ 1 := by decide +kernel
    exact hne (congrArg Subtype.val h)

private theorem y_order : orderOf y = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have hne : (y : Equiv.Perm (Fin 24)) ≠ 1 := by decide +kernel
    exact hne (congrArg Subtype.val h)

private theorem x_commute_y : Commute x y := by
  apply Subtype.ext
  decide +kernel

private theorem y_not_mem : y ∉ zpowers x := by
  rw [mem_zpowers_iff_mem_range_orderOf, x_order]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hh : ∀ i : Fin 3,
      (y : Equiv.Perm (Fin 24)) ≠ (x : Equiv.Perm (Fin 24)) ^ i.val := by
    decide +kernel
  exact hh ⟨i, Finset.mem_range.mp hi⟩ (congrArg Subtype.val he).symm

/-- A concrete elementary abelian subgroup of the fixed M₂₄ carrier. -/
noncomputable def elementaryNine : Subgroup M24 := zpowers x ⊔ zpowers y

/-- Both the elementary-abelian assertion and the exact order are proved. -/
theorem elementaryNine_properties :
    IsElementaryAbelian 3 elementaryNine ∧ Nat.card elementaryNine = 9 := by
  let : IsElementaryAbelian 3 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (x_order ▸ pow_orderOf_eq_one x)
  have hc : Nat.card (zpowers x) = 3 ^ 1 := by
    rw [Nat.card_zpowers, x_order]; norm_num
  have hfix : zpowers x ≤ centralizer ({y} : Set M24) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr x_commute_y.eq
  exact IsElementaryAbelian.fixed_join_card (zpowers x) y y_order
    ((zpowers x).disjoint_zpowers_of_prime_order_not_mem y y_order y_not_mem)
    hfix hc

/-- The common fixed point and the nine-point orbit rule out every trio. -/
theorem elementaryNine_not_le_trioStabilizer (T : Trio) :
    ¬ elementaryNine ≤ trioStabilizer T := by
  intro h
  have hx := (mem_trioStabilizer_iff T x).mp
    (h ((le_sup_left : zpowers x ≤ elementaryNine) (mem_zpowers x)))
  have hy := (mem_trioStabilizer_iff T y).mp
    (h ((le_sup_right : zpowers y ≤ elementaryNine) (mem_zpowers y)))
  exact no_trio T hx hy

private noncomputable def translatedTrio (T : Trio) (g : M24) : Trio where
  parts := g • T.parts
  card := by rw [Finset.card_smul_finset, T.card]
  octad A hA := by
    obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.mp hA
    have hm : B ∈ (m24Blocks : Set (Finset (Fin 24))) := T.octad B hB
    have him := Set.smul_mem_smul_set (a := (g : Equiv.Perm (Fin 24))) hm
    rw [(mem_M24_iff _).mp g.property] at him
    exact him
  disjoint A hA B hB hne := by
    obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨D, hD, rfl⟩ := Finset.mem_smul_finset.mp hB
    have hd := T.disjoint C hC D hD (fun he => hne (congrArg (g • ·) he))
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨c, hc, hec⟩ := Finset.mem_smul_finset.mp ha
    obtain ⟨d, hdm, hed⟩ := Finset.mem_smul_finset.mp hb
    have he : c = d := smul_left_cancel g (hec.trans hed.symm)
    exact Finset.disjoint_left.mp hd hc (he ▸ hdm)
  cover := by
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    have hm : g⁻¹ • a ∈ T.parts.biUnion id := by
      rw [T.cover]; simp
    obtain ⟨B, hB, hBa⟩ := Finset.mem_biUnion.mp hm
    apply Finset.mem_biUnion.mpr
    refine ⟨g • B, Finset.smul_mem_smul_finset hB, ?_⟩
    simpa using Finset.smul_mem_smul_finset (a := g) hBa

/-- In particular this subgroup cannot be placed in any translated standard
trio stabilizer. This uses the literal translated octad partition. -/
theorem elementaryNine_not_le_conjugateTrioStabilizer (g : M24) :
    ¬ elementaryNine ≤ conjugateTrioStabilizer g :=
  elementaryNine_not_le_trioStabilizer (translatedTrio standardTrio g)


end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TrioObstruction

end
