module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Card

/-!
# A hyperplane cannot isolate a point of a nine-element binary orbit

Let a group act by automorphisms on an elementary abelian group E of
order thirty-two. An order-sixteen subgroup U cannot meet a nine-element
orbit in exactly one point z.

Choose a binary linear functional f with kernel U. For each orbit point
v different from z, transport f by an actor taking z to v, and add f.
On the other eight orbit points these functionals form the dual coordinate
family. Those eight points are therefore linearly independent, giving an
injection of the binary space of order 256 into E, a contradiction.

This elementary linear-algebra argument applies to Parrott's order-thirty-two
case on p.676 of *A characterization of the Tits' simple group* (1972).
It uses the actual index-two intersection and weak closure directly, with
no solvability or automorphism-group classification assumption.
-/

open Subgroup MulAction
open scoped IsMulCommutative

/-- A half-sized subgroup cannot isolate one point of a nine-point orbit in binary rank five. -/
public theorem not_card_orbit_nine_of_binary_thirtyTwo_and_half_subgroup
    {E M : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    [Group M] [MulDistribMulAction M E]
    (hE : Nat.card E = 32) (U : Subgroup E) (hU : Nat.card U = 16)
    (z : E) (hz : z ∈ U)
    (hinter : ∀ v : E, v ∈ orbit M z → v ∈ U → v = z) :
    Nat.card (orbit M z) ≠ 9 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := Additive E
  let L : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 U.toAddSubgroup
  have hL : L < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    have hUtop : U = ⊤ := by
      ext a
      change Additive.ofMul a ∈ L ↔ a ∈ (⊤ : Subgroup E)
      rw [heq]
      simp
    rw [hUtop, card_top, hE] at hU
    omega
  obtain ⟨f, hf, hLf⟩ := L.exists_le_ker_of_lt_top hL
  have hF2 : Nat.card (ZMod 2) = 2 := by simp
  have hbits : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.mp hf
  have hv₀one : f v₀ = 1 := (hbits _).resolve_left (by simpa using hv₀)
  have hsurj : Function.Surjective f.toAddMonoidHom := by
    intro c
    rcases hbits c with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨v₀, hv₀one⟩
  have hkerCard : Nat.card f.toAddMonoidHom.ker = 16 := by
    have hc := f.toAddMonoidHom.ker.card_mul_index
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj,
      AddSubgroup.card_top] at hc
    have hV : Nat.card V = 32 := hE
    rw [hF2, hV] at hc
    omega
  have hLeq : L.toAddSubgroup = f.toAddMonoidHom.ker :=
    AddSubgroup.eq_of_le_of_card_ge hLf (by
      change Nat.card f.toAddMonoidHom.ker ≤ Nat.card U
      rw [hkerCard, hU])
  have hfmem (v : E) : f (Additive.ofMul v) = 0 ↔ v ∈ U := by
    change Additive.ofMul v ∈ f.toAddMonoidHom.ker ↔ v ∈ U
    rw [← hLeq]
    rfl
  have hfzero (v : E) (hv : v ∈ orbit M z) : f (Additive.ofMul v) = 0 ↔ v = z :=
    ⟨fun hvf => hinter v hv ((hfmem v).mp hvf), fun hvz => hvz ▸ (hfmem z).mpr hz⟩
  have hfz : f (Additive.ofMul z) = 0 := (hfmem z).mpr hz
  intro hcard
  let I := (orbit M z \ {z} : Set E)
  let : Fintype I := Fintype.ofFinite I
  have hIcard : Nat.card I = 8 := by
    change (orbit M z \ {z}).ncard = 8
    rw [Set.ncard_sdiff_singleton_of_mem (mem_orbit_self z)]
    change Nat.card (orbit M z) - 1 = 8
    rw [hcard]
  let v : I → V := fun i => Additive.ofMul (i : E)
  choose g hg using fun i : I => (show ∃ m : M, m • z = (i : E) from i.property.1)
  let act (m : M) : V →ₗ[ZMod 2] V :=
    (MulEquiv.toAdditive (MulDistribMulAction.toMulAut M E m)).toAddMonoidHom.toZModLinearMap 2
  let test (i : I) : V →ₗ[ZMod 2] ZMod 2 := f.comp (act (g i)⁻¹) + f
  have hfv (i : I) : f (v i) = 1 := by
    apply (hbits _).resolve_left
    intro hzero
    exact i.property.2 ((hfzero i i.property.1).mp hzero)
  have htest (i j : I) : test i (v j) = if i = j then 1 else 0 := by
    change f (Additive.ofMul ((g i)⁻¹ • (j : E))) + f (v j) = _
    rw [hfv]
    by_cases hij : i = j
    · subst j
      have heq : (g i)⁻¹ • (i : E) = z := by rw [← hg i, inv_smul_smul]
      rw [if_pos rfl, heq, hfz, zero_add]
    · have hmem : (g i)⁻¹ • (j : E) ∈ orbit M z :=
        mapsTo_smul_orbit (g i)⁻¹ z j.property.1
      have hne : (g i)⁻¹ • (j : E) ≠ z := by
        intro heq
        have hh := congrArg (fun a : E => g i • a) heq
        rw [smul_inv_smul] at hh
        exact hij (Subtype.ext ((hg i).symm.trans hh.symm))
      have hone : f (Additive.ofMul ((g i)⁻¹ • (j : E))) = 1 :=
        (hbits _).resolve_left (fun hh => hne ((hfzero _ hmem).mp hh))
      rw [if_neg hij, hone]
      decide
  have hlin : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hh := congrArg (test i) hc
    simpa only [map_sum, map_smul, htest, smul_ite, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_zero] using hh
  have hbound := Nat.card_le_card_of_injective (Fintype.linearCombination (ZMod 2) v)
    (linearIndependent_iff_injective_fintypeLinearCombination.mp hlin)
  rw [Nat.card_fun, hF2, hIcard] at hbound
  change 256 ≤ Nat.card E at hbound
  omega
