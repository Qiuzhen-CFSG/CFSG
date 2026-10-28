module

public import Theory.GroupTheory.ClassTwoCommutator
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.BinaryExpansion
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Derived order in a central elementary-eight extension

A finite group with a central normal subgroup and elementary abelian
quotient of order eight has derived subgroup of order at most eight.
No chosen generators or presentation are required as hypotheses.

The binary vector-space structure supplies three quotient generators.
Lift them to the group. The class-two commutator homomorphisms show that
the three pairwise commutators generate the derived subgroup. Centrality
of squares makes these commutators involutions, so their subgroup has at
most eight elements, represented by binary products.

This is the terminal counting argument for Sz(8) in GLS3, section 6.3,
printed p.337 (`refs/KGroup/GLS3/chapter6.tex`, lines 315–317).
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

private theorem exists_three_generators
    {Q : Type*} [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
    (hcard : Nat.card Q = 8) :
    ∃ v : Fin 3 → Q, closure (Set.range v) = ⊤ := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive Q) = 2 ^ 3 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    change Nat.card Q = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (2 : ℕ) ^ 3 = 8 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive Q) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive Q) hdim
  let v : Fin 3 → Q := fun i => (b i).toMul
  let H := closure (Set.range v)
  let W : Submodule (ZMod 2) (Additive Q) := AddSubgroup.toZModSubmodule 2 H.toAddSubgroup
  have hW : W = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change v i ∈ H
    exact subset_closure ⟨i, rfl⟩
  refine ⟨v, top_unique ?_⟩
  intro x _
  have hx : Additive.ofMul x ∈ W := by rw [hW]; trivial
  exact hx

private theorem eq_top_of_lift_generators
    {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (g : Fin 3 → G) (hgen : closure (Set.range (fun i => f (g i))) = ⊤)
    (H : Subgroup G) (hker : f.ker ≤ H) (hg : ∀ i, g i ∈ H) : H = ⊤ := by
  have hmap : H.map f = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact (closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact mem_map_of_mem f (hg i))
  rw [← comap_map_eq_self hker, hmap, comap_top]

private theorem derived_le_of_lift_generators
    {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hker : f.ker ≤ center G) (hd : _root_.commutator G ≤ center G)
    (g : Fin 3 → G) (hgen : closure (Set.range (fun i => f (g i))) = ⊤)
    (C : Subgroup G) (hpair : ∀ i j, ⁅g i, g j⁆ ∈ C) :
    _root_.commutator G ≤ C := by
  have row (x : G) (hx : ∀ i, ⁅x, g i⁆ ∈ C) (y : G) : ⁅x,y⁆ ∈ C := by
    have htop : C.comap (ClassTwo.commutatorHom hd x) = ⊤ := by
      apply eq_top_of_lift_generators f g hgen
      · intro n hn
        change ⁅x,n⁆ ∈ C
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hker hn) x)]
        exact C.one_mem
      · exact hx
    exact show y ∈ C.comap (ClassTwo.commutatorHom hd x) from htop ▸ mem_top y
  apply commutator_le.mpr
  intro x _ y _
  apply row x _ y
  intro i
  have hi := C.inv_mem (row (g i) (hpair i) x)
  simpa only [commutatorElement_inv] using hi

/-- A central elementary-eight quotient forces the derived group to have
order at most eight. The three quotient generators are constructed internally. -/
public theorem card_commutator_le_eight_of_central_elementary_eight_quotient
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G)
    [IsElementaryAbelian 2 (G ⧸ N)] (hcard : Nat.card (G ⧸ N) = 8) :
    Nat.card (_root_.commutator G) ≤ 8 := by
  classical
  let q := QuotientGroup.mk' N
  have hd : _root_.commutator G ≤ center G :=
    (Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (G ⧸ N))).trans hN
  have hsq (x : G) : x ^ 2 ∈ center G := by
    apply hN
    apply (QuotientGroup.eq_one_iff (N := N) _).mp
    change q (x ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ N)) _
  have hcomm_sq (x y : G) : ⁅x,y⁆ ^ 2 = 1 := by
    have hp := map_pow (ClassTwo.commutatorHom hd x) y 2
    change ⁅x,y ^ 2⁆ = ⁅x,y⁆ ^ 2 at hp
    rw [← hp]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hsq y) x)
  obtain ⟨v, hv⟩ := exists_three_generators hcard
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice (fun i => QuotientGroup.mk'_surjective N (v i))
  have hgen : closure (Set.range (fun i => q (g i))) = ⊤ := by
    simpa only [q, hg] using hv
  let c : Fin 3 → center G := ![
    ⟨⁅g 0,g 1⁆, hd (commutator_mem_commutator (mem_top _) (mem_top _))⟩,
    ⟨⁅g 0,g 2⁆, hd (commutator_mem_commutator (mem_top _) (mem_top _))⟩,
    ⟨⁅g 1,g 2⁆, hd (commutator_mem_commutator (mem_top _) (mem_top _))⟩]
  let C := closure (Set.range c)
  let K := C.map (center G).subtype
  have hc (i : Fin 3) : (c i : G) ∈ K :=
    mem_map_of_mem (center G).subtype (subset_closure ⟨i, rfl⟩)
  have hpair : ∀ i j, ⁅g i,g j⁆ ∈ K := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp
    · exact hc 0
    · exact hc 1
    · rw [← commutatorElement_inv]; exact K.inv_mem (hc 0)
    · simp
    · exact hc 2
    · rw [← commutatorElement_inv]; exact K.inv_mem (hc 1)
    · rw [← commutatorElement_inv]; exact K.inv_mem (hc 2)
    · simp
  have hderived : _root_.commutator G ≤ K :=
    derived_le_of_lift_generators q (by simpa only [q, QuotientGroup.ker_mk'] using hN)
      hd g hgen K hpair
  have hcsq (i : Fin 3) : c i * c i = 1 := by
    apply Subtype.ext
    change (c i : G) * (c i : G) = 1
    rw [← pow_two]
    fin_cases i <;> exact hcomm_sq _ _
  let expansion : (Fin 3 → Bool) → C := fun b =>
    ⟨∏ i, if b i then c i else 1, C.prod_mem (fun i _ => by
      split <;> [exact subset_closure ⟨i, rfl⟩; exact C.one_mem])⟩
  have hsurj : Function.Surjective expansion := by
    intro x
    obtain ⟨b, hb⟩ := Theory.GroupTheory.exists_bool_prod_of_mem_closure_range c hcsq x.property
    exact ⟨b, Subtype.ext hb.symm⟩
  have hC : Nat.card C ≤ 8 := by
    have hb := Nat.card_le_card_of_surjective expansion hsurj
    simpa using hb
  have hK : Nat.card K = Nat.card C :=
    (Nat.card_congr (C.equivMapOfInjective (center G).subtype (center G).subtype_injective).toEquiv).symm
  exact (card_le_of_le hderived).trans (hK ▸ hC)
