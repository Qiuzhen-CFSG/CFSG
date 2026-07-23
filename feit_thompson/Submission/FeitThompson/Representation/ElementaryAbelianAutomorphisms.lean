/-
Authors: Yusen Tang
-/

module

public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.ZMod.Torsion
public import Submission.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import Submission.FeitThompson.Burnside.NormalComplement
public import Submission.FeitThompson.Extraspecial
public import Submission.FeitThompson.LinearAlgebra.BlockElementaryMap
public import Submission.FeitThompson.Representation.ConjugateRep
public import Submission.FeitThompson.BGsection2.EndFieldRep
public import Submission.FeitThompson.Representation.TwoDimensionalOddOrder

open Representation
open MonoidAlgebra
open Module
open Module.End
open Polynomial
open scoped DirectSum
open scoped BigOperators
open scoped TensorProduct
open scoped MonoidAlgebra
open scoped Function
open scoped IsMulCommutative
/-
**Kind**: Theorem
**Note**: Lemma 2.7
**Stmt**:
Let $p,q$ be distinct primes.
Let $P,Q$ be elementary abelian group of $p^2, q^2$ respectively.
Assume that $Q \subseteq \Aut(P)$.
Then
(a) $q$ divides $(p - 1)$.
(b) There exists $\alpha \in Q^\#$ and an integer $r$ such that $x^\alpha = x^r$ for every $x \in P, r^q \equiv 1 (\mod p), r \not\equiv 1 (\mod p)$.
-/

def lemma_2_7_toEnd
    (p : ℕ) [Fact p.Prime]
    {P Q : Type*} [Group P] [Group Q] [IsElementaryAbelian p P]
    (i : Q →* MulAut P) (α : Q) :
  Module.End (ZMod p) (Additive P) := {
    toFun := fun x ↦ Additive.ofMul ((i α) (Additive.toMul x))
    map_add' := fun x y ↦ by
      rw [toMul_add, map_mul]
      rfl
    map_smul' := fun m x ↦ by
      have (y : Additive P): m • y = m.val • y := by
        nth_rw 1 [← ZMod.natCast_zmod_val m, Nat.cast_smul_eq_nsmul]
      rw [RingHom.id_apply, this, this, toMul_nsmul, map_pow]
      rfl
  }

def lemma_2_7_representation
    (p : ℕ) [Fact p.Prime]
    {P Q : Type*} [Group P] [Group Q] [IsElementaryAbelian p P]
    (i : Q →* MulAut P) :
  Representation (ZMod p) Q (Additive P) := {
    toFun := fun q ↦ lemma_2_7_toEnd p i q
    map_one' := by
      ext x
      have : Additive.ofMul ((i (1 : Q)) (Additive.toMul x)) = x := by
        rw [map_one, MulAut.one_apply, ofMul_toMul]
      exact this
    map_mul' := fun q₁ q₂ ↦ by
      ext x
      simp only [Module.End.mul_apply, EmbeddingLike.apply_eq_iff_eq]
      have : Additive.toMul (Additive.ofMul ((i (q₁ * q₂)) (Additive.toMul x))) =
      Additive.toMul (Additive.ofMul ((i q₁) ((Additive.toMul (Additive.ofMul ((i q₂) (Additive.toMul x))))))) := by
        simp only [map_mul, MulAut.mul_apply, toMul_ofMul]
      exact this
  }

set_option backward.isDefEq.respectTransparency false in
lemma lemma_2_7_main_1
    {p q : ℕ} [factp : Fact p.Prime] [factq : Fact q.Prime] (hne : p ≠ q)
    {P Q : Type*} [Group P] [Group Q] [IsElementaryAbelian p P] [inst : IsElementaryAbelian q Q]
    (hp : Nat.card P = p ^ 2) (hq : Nat.card Q = q ^ 2)
    {i : Q →* MulAut P} (hi : Function.Injective i) :
    ∃ v₁ v₂ : Additive P,
    (Set.range (lemma_2_7_toEnd p i) : Set (Module.End (ZMod p) (Additive P))) ≤ {β |
    ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} ∧ AddSubgroup.closure {v₁, v₂} = ⊤ ∧ v₁ ≠ 0 ∧ v₂ ≠ 0 := by
  have : Finite P := by
    apply Nat.finite_of_card_ne_zero
    rw [hp]
    exact Ne.symm (NeZero.ne' (p ^ 2))
  have : Finite Q := by
    apply Nat.finite_of_card_ne_zero
    rw [hq]
    exact Ne.symm (NeZero.ne' (q ^ 2))
  have : Fintype Q := Fintype.ofFinite Q
  have : NeZero ((Fintype.card Q) : ZMod p) := by
    rw [Fintype.card_eq_nat_card, hq]
    refine NeZero.of_not_dvd (ZMod p) ?_
    apply (Nat.Prime.dvd_of_dvd_pow factp.1).mt
    rw [Nat.prime_dvd_prime_iff_eq factp.1 factq.1]
    exact hne

  let ρ := (lemma_2_7_representation p i)
  have hfaithful : Function.Injective ρ :=
    fun _ _ he ↦ hi (MulEquiv.ext_iff.mpr (LinearMap.congr_fun he))

  have : ¬ IsIrreducible ρ := by
    by_contra
    have := center_cyclic_of_representation_faithful_irreducible ρ hfaithful
    have : IsCyclic Q := by
      have he : Subgroup.center Q = ⊤ := CommGroup.center_eq_top
      rw [he] at this
      rcases this with ⟨g, hg⟩
      use g
      intro a
      rcases hg ⟨a, Subgroup.mem_top a⟩ with ⟨b, hb⟩
      use b
      simp only at ⊢ hb
      have : (g.val ^ b) = (⟨a, Subgroup.mem_top a⟩ : (⊤ : Subgroup Q)).val :=
        hb.symm ▸ Eq.symm (Subgroup.coe_zpow ⊤ g b)
      exact this
    rcases (isCyclic_iff_exists_orderOf_eq_natCard.mp this) with ⟨g, hg⟩
    have := orderOf_dvd_of_pow_eq_one (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p q Q) g)
    rw [hg, hq] at this
    exact Nat.not_pos_pow_dvd (Nat.Prime.one_lt factq.1) Nat.one_lt_two this
  have : Nontrivial (Subrepresentation ρ) := by
    refine nontrivial_of_ne ⊤ ⊥ ?_
    suffices h : Nat.card (⊤ : Set (Additive P)) ≠ Nat.card ({0} : Set (Additive P)) by exact SetLike.coe_ne_coe.mp fun a ↦ h (congrArg Nat.card (congrArg Set.Elem a))
    have : Nat.card (⊤ : Set (Additive P)) = Nat.card P := by
      refine Nat.card_congr {
        toFun := fun m ↦ m.val
        invFun := fun m ↦ ⟨Additive.ofMul m, Set.mem_preimage.mp trivial⟩
      }
    rw [this, hp, Nat.card_unique, ne_eq, Nat.pow_eq_one.not]
    push Not
    exact ⟨Nat.Prime.ne_one factp.1, two_ne_zero⟩
  have : ¬ (∀ (a : Subrepresentation ρ), a = ⊥ ∨ a = ⊤) := by tauto
  push Not at this

  rcases this with ⟨a, ha⟩
  let a' := by
    refine submoduleOfSMulMem (M := Q) (V := ρ.asModule) a.toSubmodule ?_
    intro q v hv
    simp only [of_apply, single_smul, one_smul]
    have hv' : (ρ.asModuleEquiv v) ∈ a.toSubmodule := (Submodule.mem_toAddSubgroup a.toSubmodule).mp hv
    exact a.apply_mem_toSubmodule q hv'
  have hss : ∃ b', IsCompl a' b' := MonoidAlgebra.Submodule.exists_isCompl' (k := ZMod p) (G := Q) (V := ρ.asModule) a'
  rcases hss with ⟨b', hb'⟩

  have hle2 {a : ℕ} (h1 : a ≤ 2) : a = 0 ∨ a = 1 ∨ a = 2 := by
    omega
  have hρ : Nat.card ρ.asModule = p ^ 2 := by
    have : Nat.card ρ.asModule = Nat.card P := by
      simp_all [ρ]
      obtain ⟨left, right⟩ := ha
      exact hp
    rw [this, hp]
  have : Finite ρ.asModule := by
    apply Nat.finite_of_card_ne_zero
    rw [hρ]
    exact Ne.symm (NeZero.ne' (p ^ 2))
  have : FiniteDimensional (ZMod p) ρ.asModule :=
    Module.Finite.of_finite
  have hdim : Module.rank (ZMod p) ρ.asModule = 2 := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := ρ.asModule)
    simp only [Nat.card_eq_fintype_card, ZMod.card, hρ] at this
    have : Module.finrank (ZMod p) ρ.asModule = 2 := by
      have hinj := Nat.pow_right_injective (a := p) (Nat.Prime.two_le factp.1)
      exact (hinj this).symm
    rw [← Module.finrank_eq_rank, this]
    rfl
  have he'a : Nat.card a' = Nat.card a := by
    simp_all [ρ, a']
    obtain ⟨left, right⟩ := ha
    rfl
  have hdima' : Module.rank (ZMod p) a' = 1 := by
    have hn0 : Nat.card a ≠ 1 := by
      apply (AddSubgroup.card_eq_one (H := a.toSubmodule.toAddSubgroup)).mp.mt
      suffices h : (a : Set (Additive P)) ≠ {0} by exact SetLike.coe_ne_coe.mp h
      exact SetLike.coe_ne_coe.mpr ha.1
    have hn2 : Nat.card a ≠ p ^ 2 := by
      rw [← hp]
      apply (AddSubgroup.card_eq_iff_eq_top (H := a.toSubmodule.toAddSubgroup)).mp.mt
      suffices h : (a : Set (Additive P)) ≠ Set.univ by exact SetLike.coe_ne_coe.mp h
      exact SetLike.coe_ne_coe.mpr ha.2
    have hle : Nat.card a ≤ p ^ 2 := by
      rw [← hp]
      exact Finite.card_subtype_le (Membership.mem a)
    have : FiniteDimensional (ZMod p) a' :=
      Module.Finite.of_finite
    have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := a')
    simp only [Nat.card_eq_fintype_card, ZMod.card, he'a] at hc
    have : Module.finrank (ZMod p) a' = 1:= by
      rw [hc] at hle hn2 hn0
      rw [pow_le_pow_iff_right₀ (Nat.Prime.one_lt factp.1)] at hle
      rcases hle2 hle with h | h | h
      · exfalso
        rw [h, pow_zero] at hn0
        exact absurd (Eq.refl 1) hn0
      · exact h
      · exfalso
        rw [h] at hn2
        exact absurd (Eq.refl (p ^ 2)) hn2
    rw [← Module.finrank_eq_rank, this]
    rfl
  have hdimb' : Module.rank (ZMod p) b' = 1 := by
    let b : Subrepresentation ρ := {
      toSubmodule := (mapSubmodule ρ).symm b'
      apply_mem_toSubmodule := fun x v hv ↦ by
        have : ((ρ.mapSubmodule.symm b') : Submodule (ZMod p) (Additive P)) ∈ ρ.invtSubmodule := SetLike.coe_mem (ρ.mapSubmodule.symm b')
        have := (mem_invtSubmodule ρ).mp this x
        exact (End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp this v hv
    }
    have he' : Nat.card b' = Nat.card b := rfl
    have hn0 : Nat.card b ≠ 1 := by
      rw [← he']
      apply (AddSubgroup.card_eq_one (H := b'.toAddSubgroup)).mp.mt
      suffices h : (b' : Set ρ.asModule) ≠ {0} by exact SetLike.coe_ne_coe.mp h
      suffices h : b' ≠ ⊥ by exact SetLike.coe_ne_coe.mpr h
      by_contra h
      have ha' := hb'.codisjoint
      rw [codisjoint_iff, h, sup_bot_eq] at ha'
      have : a = ⊤ := by
        suffices h : (a : Set (Additive P)) = (⊤ : Subrepresentation ρ) by
          rw [← not_ne_iff] at h ⊢
          exact SetLike.coe_ne_coe.mpr.mt h
        have : ((⊤ : Subrepresentation ρ) : Set (Additive P)) = Set.univ := rfl
        rw [this]
        suffices h : a.toSubmodule.toAddSubgroup = (⊤ : AddSubgroup (Additive P)) by
          rw [← not_ne_iff] at h ⊢
          exact SetLike.coe_ne_coe.mp.mt h
        apply (AddSubgroup.card_eq_iff_eq_top (H := a.toSubmodule.toAddSubgroup)).mp
        have : Nat.card (Additive P) = Nat.card P := rfl
        rw [this]
        have : Nat.card a.toSubmodule.toAddSubgroup = Nat.card a := rfl
        rw [this, ← he'a]
        have : Nat.card a' = Nat.card a'.toAddSubgroup := rfl
        rw [this]
        have : a'.toAddSubgroup = (⊤ : AddSubgroup ρ.asModule) := by
          rw [ha']
          exact Submodule.top_toAddSubgroup
        rw [← AddSubgroup.card_eq_iff_eq_top (H := a'.toAddSubgroup)] at this
        exact this
      exact ha.2 this
    have hn2 : Nat.card b ≠ p ^ 2 := by
      rw [← he', ← hρ]
      apply (AddSubgroup.card_eq_iff_eq_top (H := b'.toAddSubgroup)).mp.mt
      suffices h : (b' : Set ρ.asModule) ≠ Set.univ by exact SetLike.coe_ne_coe.mp h
      suffices h : b' ≠ ⊤ by exact SetLike.coe_ne_coe.mpr h
      by_contra h
      have ha' := hb'.disjoint
      rw [disjoint_iff, h, inf_top_eq] at ha'
      have : a = ⊥ := by
        suffices h : (a : Set (Additive P)) = (⊥ : Subrepresentation ρ) by
          rw [← not_ne_iff] at h ⊢
          exact SetLike.coe_ne_coe.mpr.mt h
        have : ((⊥ : Subrepresentation ρ) : Set (Additive P)) = {0} := rfl
        rw [this]
        suffices h : a.toSubmodule.toAddSubgroup = (⊥ : AddSubgroup (Additive P)) by
          rw [← not_ne_iff] at h ⊢
          exact SetLike.coe_ne_coe.mp.mt h
        apply (AddSubgroup.card_eq_one (H := a.toSubmodule.toAddSubgroup)).mp
        have : Nat.card a.toSubmodule.toAddSubgroup = Nat.card a := rfl
        rw [this, ← he'a]
        have : Nat.card a' = Nat.card a'.toAddSubgroup := rfl
        rw [this]
        have : a'.toAddSubgroup = (⊥ : AddSubgroup ρ.asModule) := by
          rw [ha']
          exact Submodule.bot_toAddSubgroup
        rw [← AddSubgroup.card_eq_one (H := a'.toAddSubgroup)] at this
        exact this
      exact ha.1 this
    have hle : Nat.card b ≤ p ^ 2 := by
      rw [← hp]
      exact Finite.card_subtype_le (Membership.mem b)
    have : FiniteDimensional (ZMod p) b' :=
      Module.Finite.of_finite
    have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := b')
    simp only [Nat.card_eq_fintype_card, ZMod.card, he'] at hc
    have : Module.finrank (ZMod p) b' = 1:= by
      rw [hc] at hle hn2 hn0
      rw [pow_le_pow_iff_right₀ (Nat.Prime.one_lt factp.1)] at hle
      rcases hle2 hle with h | h | h
      · exfalso
        rw [h, pow_zero] at hn0
        exact absurd (Eq.refl 1) hn0
      · exact h
      · exfalso
        rw [h] at hn2
        exact absurd (Eq.refl (p ^ 2)) hn2
    rw [← Module.finrank_eq_rank, this]
    rfl

  have hv₁' := (rank_eq_one_iff (K := ZMod p) (V := a')).mp hdima'
  have hv₂' := (rank_eq_one_iff (K := ZMod p) (V := b')).mp hdimb'
  rcases hv₁' with ⟨v₁', hv₁'n, hv₁'⟩
  rcases hv₂' with ⟨v₂', hv₂'n, hv₂'⟩
  simp only [Subtype.forall] at hv₁' hv₂'
  let j := ρ.asModuleEquiv
  let v₁ : Additive P := j v₁'.val
  let v₂ : Additive P := j v₂'.val
  use v₁, v₂
  constructor
  · intro β ⟨x, hx⟩
    simp only [exists_and_left, Set.mem_setOf_eq]
    have : single x (1 : ZMod p) • j.symm v₁ ∈ a' := by
      apply Submodule.smul_mem'
      simp only [v₁, Submodule.carrier_eq_coe, LinearEquiv.symm_apply_apply, Subtype.coe_prop]
    simp only [j, single_smul, one_smul, LinearEquiv.apply_symm_apply] at this
    rcases (hv₁' (ρ x v₁) this) with ⟨l₁, hl₁⟩
    have hl₁s : l₁ • v₁ = ρ x v₁ := by
      trans (l₁ • v₁').val
      · rfl
      · rw [hl₁]
    have : single x (1 : ZMod p) • j.symm v₂ ∈ b' := by
      apply Submodule.smul_mem'
      simp only [v₂, Submodule.carrier_eq_coe, LinearEquiv.symm_apply_apply, Subtype.coe_prop]
    simp only [j, single_smul, one_smul, LinearEquiv.apply_symm_apply] at this
    rcases (hv₂' (ρ x v₂) this) with ⟨l₂, hl₂⟩
    have hl₂s : l₂ • v₂ = ρ x v₂ := by
      trans (l₂ • v₂').val
      · rfl
      · rw [hl₂]
    have hl₁p : β v₁ = l₁ • v₁ := by
      rw [hl₁s, ← hx]
      rfl
    have hl₂p : β v₂ = l₂ • v₂ := by
      rw [hl₂s, ← hx]
      rfl
    have hp (n : ℕ) {v : Additive P} {l : ZMod p} (h : β v = l • v) : (β ^ n) v = (l ^ n) • v := by
      induction n with
      | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
      | succ n hn =>
        rw [pow_succ', Module.End.mul_apply, hn, map_smul, h, smul_smul, pow_succ]
    use l₁
    have hβ : β ^ q = 1 := by
      ext m
      rw [← hx, Module.End.one_apply, EmbeddingLike.apply_eq_iff_eq]
      have (q₁ q₂ : Q) : (lemma_2_7_toEnd p i q₁) * (lemma_2_7_toEnd p i q₂) = lemma_2_7_toEnd p i (q₁ * q₂) := by
        ext m
        simp only [Module.End.mul_apply, EmbeddingLike.apply_eq_iff_eq]
        have (q : Q) (n : Additive P): (lemma_2_7_toEnd p i q) n = Additive.ofMul ((i q) (Additive.toMul n)) := rfl
        rw [this, this, this]
        simp only [toMul_ofMul, map_mul, MulAut.mul_apply]
      have (n : ℕ) : lemma_2_7_toEnd p i x ^ n = lemma_2_7_toEnd p i (x ^ n) := by
        ext m
        induction n with
        | zero =>
          simp only [EmbeddingLike.apply_eq_iff_eq, pow_zero, Module.End.one_apply]
          have : m = Additive.ofMul ((i 1) (Additive.toMul m)) := by
            simp only [map_one, MulAut.one_apply, ofMul_toMul]
          exact this
        | succ n hn =>
          simp only [EmbeddingLike.apply_eq_iff_eq] at ⊢ hn
          rw [pow_succ', Module.End.mul_apply, hn, ← Module.End.mul_apply, this, pow_succ']
      rw [this, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp inst.exponent_dvd_p x]
      have : Additive.ofMul ((i 1) (Additive.toMul m)) = m := by
        simp only [map_one, MulAut.one_apply, ofMul_toMul]
      exact this
    constructor
    exact hl₁p
    use l₂
    constructor
    exact hl₂p
    constructor
    · have := hp q hl₁p
      rw [hβ, Module.End.one_apply] at this
      have : (l₁ ^ q - (1 : ZMod p)) • v₁ = 0 := by
        calc
          (l₁ ^ q - (1 : ZMod p)) • v₁ = l₁ ^ q • v₁ - (1 : ZMod p) • v₁ := by rw [sub_smul]
          _ = l₁ ^ q • v₁ - v₁ := by rw [one_smul]
          _ = 0 := by rw [← this, sub_self]
      rw [smul_eq_zero] at this
      contrapose! this
      constructor
      · exact sub_ne_zero.mpr this
      · by_contra
        have hv₁n : v₁ ≠ 0 := Subtype.coe_ne_coe.mpr hv₁'n
        exact hv₁n this
    · have := hp q hl₂p
      rw [hβ, Module.End.one_apply] at this
      have : (l₂ ^ q - (1 : ZMod p)) • v₂ = 0 := by
        calc
          (l₂ ^ q - (1 : ZMod p)) • v₂ = l₂ ^ q • v₂ - (1 : ZMod p) • v₂ := by rw [sub_smul]
          _ = l₂ ^ q • v₂ - v₂ := by rw [one_smul]
          _ = 0 := by rw [← this, sub_self]
      rw [smul_eq_zero] at this
      contrapose! this
      constructor
      · exact sub_ne_zero.mpr this
      · by_contra
        have hv₂n : v₂ ≠ 0 := Subtype.coe_ne_coe.mpr hv₂'n
        exact hv₂n this
  · have hv₁ : v₁ ≠ 0 := by
      suffices h : j v₁ ≠ 0 by exact (LinearEquiv.map_ne_zero_iff j).mpr h
      have : v₁'.val ≠ 0 := by
        contrapose hv₁'n
        exact Submodule.coe_eq_zero.mp hv₁'n
      exact this
    have hv₂ : v₂ ≠ 0 := by
      suffices h : j v₂ ≠ 0 by exact (LinearEquiv.map_ne_zero_iff j).mpr h
      have : v₂'.val ≠ 0 := by
        contrapose hv₂'n
        exact Submodule.coe_eq_zero.mp hv₂'n
      exact this
    refine ⟨?_, hv₁, hv₂⟩
    ext x
    constructor
    · intro h
      exact AddSubgroup.mem_top x
    · intro h
      have hx : x ∈ (⊤ : Submodule (ZMod p)[Q] ρ.asModule) := h
      rw [← hb'.sup_eq_top] at hx
      rcases (Submodule.mem_sup (M := ρ.asModule)).mp hx with ⟨x₁, hx₁, x₂, hx₂, hx_eq⟩
      rcases hv₁' x₁ hx₁ with ⟨r₁, hr₁⟩
      rcases hv₂' x₂ hx₂ with ⟨r₂, hr₂⟩
      have h1 : r₁ • v₁ = x₁ := by
        trans (r₁ • v₁').val
        · rfl
        · rw [hr₁]
      have h2 : r₂ • v₂ = x₂ := by
        trans (r₂ • v₂').val
        · rfl
        · rw [hr₂]
      have (r : ZMod p) (v : Additive P): @Nat.cast ℤ instNatCastInt r.val • v = r • v := by
        have : @Nat.cast ℤ instNatCastInt r.val • v = r.val • v := by exact natCast_zsmul v r.val
        nth_rw 2 [← ZMod.natCast_zmod_val r]
        rw [this, Nat.cast_smul_eq_nsmul]
      rw [AddSubgroup.mem_closure_pair]
      use r₁.val, r₂.val
      rw [this, this, h1, h2, hx_eq]

public theorem lemma_2_7_a
    {p q : ℕ} [Fact p.Prime] [factq : Fact q.Prime] (hne : p ≠ q)
    {P Q : Type*} [Group P] [Group Q] [IsElementaryAbelian p P] [IsElementaryAbelian q Q]
    (hp : Nat.card P = p ^ 2) (hq : Nat.card Q = q ^ 2)
    {i : Q →* MulAut P} (hi : Function.Injective i) :
    q ∣ p - 1 := by
  rcases lemma_2_7_main_1 hne hp hq hi with ⟨v₁, v₂, hle, hcl, _, _⟩
  have hf : Finite {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} := by
    suffices h : Finite (Module.End (ZMod p) (Additive P)) by exact Subtype.finite
    let f : (Module.End (ZMod p) (Additive P)) → ((Additive P) → (Additive P)) := fun ϕ ↦ ϕ
    haveI : Finite (Additive P) := by
      apply Nat.finite_of_card_ne_zero
      have : Nat.card (Additive P) = Nat.card P := rfl
      rw [this, hp]
      exact Ne.symm (NeZero.ne' (p ^ 2))
    haveI : Finite ((Additive P) → (Additive P)) := Pi.finite
    apply Finite.of_injective f fun x y hxy ↦ ?_
    rw [DFunLike.ext_iff]
    exact fun z ↦ congrFun hxy z
  have hf' : Fintype {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} := Fintype.ofFinite _
  have : Nat.card (Set.range (lemma_2_7_toEnd p i)) = q ^ 2 := by
    rw [← hq]
    have hfaithful : Function.Injective (lemma_2_7_toEnd p i) :=
      fun _ _ he ↦ hi (MulEquiv.ext_iff.mpr (LinearMap.congr_fun he))
    exact Nat.card_range_of_injective hfaithful
  have hl : q ^ 2 ≤ Nat.card {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} := by
    rw [← this]
    exact Nat.card_mono hf hle
  by_contra hdvd
  have : (1 : Module.End (ZMod p) (Additive P)) ∈ {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} := by
    use 1, 1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> try rw [one_smul, Module.End.one_apply]
    all_goals rw [one_pow]
  have : ∀ β : {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1}, β = ⟨(1 : Module.End (ZMod p) (Additive P)), this⟩  := by
    intro ⟨β, hβ⟩
    suffices h : β = (1 : Module.End (ZMod p) (Additive P)) by exact SetCoe.ext h
    rcases hβ with ⟨l₁, l₂, hl₁, hl₂, hl₁e, hl₂e⟩
    let l₁' : (ZMod p)ˣ := Units.ofPowEqOne l₁ q hl₁e (Nat.Prime.ne_zero factq.1)
    have : l₁ = l₁' := rfl
    rw [this] at hl₁e
    have : (l₁' : ZMod p) ^ (p - 1) = 1 := by
      suffices h : l₁' ^ (p - 1) = 1 by exact (mem_rootsOfUnity' (p - 1) l₁').mp h
      rw [← ZMod.card_units, Fintype.card_eq_nat_card]
      exact pow_card_eq_one'
    have : (l₁' : ZMod p) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hl₁e, this⟩
      suffices h : q.gcd (p - 1) = 1 by rw [← this, h, pow_one]
      rw [(Nat.Prime.dvd_iff_not_coprime factq.1).not] at hdvd
      exact of_not_not hdvd
    have : l₁ = 1 := by
      rw [← this];
      rfl
    rw [this, one_smul] at hl₁
    let l₂' : (ZMod p)ˣ := Units.ofPowEqOne l₂ q hl₂e (Nat.Prime.ne_zero factq.1)
    have : l₂ = l₂' := rfl
    rw [this] at hl₂e
    have : (l₂' : ZMod p) ^ (p - 1) = 1 := by
      suffices h : l₂' ^ (p - 1) = 1 by exact (mem_rootsOfUnity' (p - 1) l₂').mp h
      rw [← ZMod.card_units, Fintype.card_eq_nat_card]
      exact pow_card_eq_one'
    have : (l₂' : ZMod p) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hl₂e, this⟩
      suffices h : q.gcd (p - 1) = 1 by rw [← this, h, pow_one]
      rw [(Nat.Prime.dvd_iff_not_coprime factq.1).not] at hdvd
      exact of_not_not hdvd
    have : l₂ = 1 := by
      rw [← this];
      rfl
    rw [this, one_smul] at hl₂
    ext v
    simp only [Module.End.one_apply, EmbeddingLike.apply_eq_iff_eq]
    set f := (β - (1 : Module.End (ZMod p) (Additive P)))
    have (v : Additive P) : β v = v ↔ f v = 0 := by
      nth_rw 2 [← Module.End.one_apply (R := ZMod p) v]
      rw [← sub_left_inj (a := (1 : Module.End (ZMod p) (Additive P)) v), sub_self]
      rfl
    rw [this] at ⊢ hl₁ hl₂
    have : v ∈ AddSubgroup.closure {v₁, v₂} := by
      rw [hcl]
      exact AddSubgroup.mem_top v
    rw [AddSubgroup.mem_closure_pair] at this
    rcases this with ⟨m, n, rfl⟩
    have : MulActionHomClass (Module.End (ZMod p) (Additive P)) ℤ (Additive P) (Additive P) := {map_smulₛₗ := LinearMap.map_smul_of_tower}
    rw [map_add, map_smul, map_smul, hl₁, hl₂, smul_zero, smul_zero, zero_add]

  have : Nat.card {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_one_of_forall_eq this
  rw [this] at hl
  contrapose hl
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.pow_le_one_iff, not_le]
  exact Nat.Prime.one_lt factq.1

lemma lemma_2_7_main_2
    {p q : ℕ} [factp : Fact p.Prime] [factq : Fact q.Prime] (hne : p ≠ q)
    {P Q : Type*} [Group P] [Group Q] [IsElementaryAbelian p P] [inst : IsElementaryAbelian q Q]
    (hp : Nat.card P = p ^ 2) (hq : Nat.card Q = q ^ 2)
    {i : Q →* MulAut P} (hi : Function.Injective i) :
    ∃ v₁ v₂ : Additive P,
    (Set.range (lemma_2_7_toEnd p i) : Set (Module.End (ZMod p) (Additive P))) = {β |
    ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} ∧ AddSubgroup.closure {v₁, v₂} = ⊤ ∧ v₁ ≠ 0 ∧ v₂ ≠ 0 := by
  rcases lemma_2_7_main_1 hne hp hq hi with ⟨v₁, v₂, hle, hcl, hv₁, hv₂⟩
  use v₁, v₂
  have hf : Finite {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} := by
    suffices h : Finite (Module.End (ZMod p) (Additive P)) by exact Subtype.finite
    let f : (Module.End (ZMod p) (Additive P)) → ((Additive P) → (Additive P)) := fun ϕ ↦ ϕ
    haveI : Finite (Additive P) := by
      apply Nat.finite_of_card_ne_zero
      have : Nat.card (Additive P) = Nat.card P := rfl
      rw [this, hp]
      exact Ne.symm (NeZero.ne' (p ^ 2))
    haveI : Finite ((Additive P) → (Additive P)) := Pi.finite
    apply Finite.of_injective f fun x y hxy ↦ ?_
    rw [DFunLike.ext_iff]
    exact fun z ↦ congrFun hxy z
  have hf' : Fintype {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} := Fintype.ofFinite _
  have hf'' : Finite (Set.range (lemma_2_7_toEnd p i) : Set (Module.End (ZMod p) (Additive P))) := Finite.Set.subset _ hle
  have hf''' : Fintype (Set.range (lemma_2_7_toEnd p i) : Set (Module.End (ZMod p) (Additive P))) := Fintype.ofFinite _
  have {A B : Set (Module.End (ZMod p) (Additive P))} [Fintype A] [Fintype B] (hle : A ≤ B) (hc : Fintype.card B ≤ Fintype.card A) : A = B := by
    let f := Set.inclusion hle
    have : Fintype (Set.range f) := Fintype.ofFinite ↑(Set.range f)
    have : Function.Injective f := Set.inclusion_injective hle
    have : Nat.card (Set.range f) = Nat.card A := Nat.card_range_of_injective this
    have hc : Fintype.card A = Fintype.card B :=
      Nat.le_antisymm (Set.card_le_card hle) hc
    have : Fintype.card (Set.range f) = Fintype.card B := by
      rw [Fintype.card_eq_nat_card, ← hc, Fintype.card_eq_nat_card, this]
    have : Set.range f = Set.univ := (set_fintype_card_eq_univ_iff _).mp this
    apply le_antisymm hle
    intro x hx
    let xb : B := ⟨x, hx⟩
    have : xb ∈ Set.range f := by
      rw [this]
      exact Set.mem_univ xb
    rcases this with ⟨xa, ha⟩
    have : x = xb.val := rfl
    rw [this]
    have : ⟨xa.val, Set.mem_of_mem_of_subset xa.prop hle⟩ = xb := by exact ha
    have : xb.val = xa.val := by rw [← this]
    rw [this]
    exact xa.2
  refine ⟨?_, hcl, hv₁, hv₂⟩
  apply this hle
  have : Nat.card (Set.range (lemma_2_7_toEnd p i)) = q ^ 2 := by
    rw [← hq]
    have hfaithful : Function.Injective (lemma_2_7_toEnd p i) :=
      fun _ _ he ↦ hi (MulEquiv.ext_iff.mpr (LinearMap.congr_fun he))
    exact Nat.card_range_of_injective hfaithful
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, this]
  set B := {β : Module.End (ZMod p) (Additive P) | ∃! l : (ZMod p) × (ZMod p), β v₁ = l.1 • v₁ ∧ β v₂ = l.2 • v₂ ∧ l.1 ^ q = 1 ∧ l.2 ^ q = 1}
  have : {β : Module.End (ZMod p) (Additive P) | ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} = B := by
    ext β
    unfold B
    simp only [exists_and_left, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases h with ⟨l₁, hl₁, l₂, hl₂, hl₁e, hl₂e⟩
      use (l₁, l₂)
      constructor
      · exact ⟨hl₁, hl₂, hl₁e, hl₂e⟩
      · intro l ⟨hl1, hl2, hl1e, hl2e⟩
        rw [hl1, ← sub_left_inj (a := l₁ • v₁), sub_self, ← sub_smul, smul_eq_zero] at hl₁
        rw [hl2, ← sub_left_inj (a := l₂ • v₂), sub_self, ← sub_smul, smul_eq_zero] at hl₂
        rcases hl₁ with h | h
        · rcases hl₂ with h' | h'
          · rw [← add_left_inj (a := l₁), sub_add, sub_self, sub_zero, zero_add] at h
            rw [← add_left_inj (a := l₂), sub_add, sub_self, sub_zero, zero_add] at h'
            rw [← h, ← h']
          · exfalso
            exact hv₂ h'
        · exfalso
          exact hv₁ h
    · intro h
      rcases h with ⟨l, hl, _⟩
      use l.1
      constructor
      · exact hl.1
      use l.2
      exact ⟨hl.2.1, hl.2.2.1, hl.2.2.2⟩
  rw [this]
  let L := {l₁ : ZMod p| l₁ ^ q = 1} ×ˢ {l₂ : ZMod p| l₂ ^ q = 1}
  let pr (β' : B) : (ZMod p) × (ZMod p) → Prop := fun l ↦ β'.val v₁ = l.1 • v₁ ∧ β'.val v₂ = l.2 • v₂ ∧ l.1 ^ q = 1 ∧ l.2 ^ q = 1
  have (β' : B) : DecidablePred (pr β') := Classical.decPred _
  have (β' : B) := Set.mem_setOf_eq ▸ β'.prop
  let f : B → (ZMod p) × (ZMod p) := fun β' ↦ Fintype.choose (pr β') (this β')
  have hap (β' : B) : (pr β') (f β') := Fintype.choose_spec (pr β') (this β')
  have : Function.Injective f := by
    intro β₁' β₂' he
    rcases hap β₁' with ⟨hβ₁'1, hβ₁'2, _, _⟩
    rcases hap β₂' with ⟨hβ₂'1, hβ₂'2, _, _⟩
    ext v
    simp only [EmbeddingLike.apply_eq_iff_eq]
    have : v ∈ AddSubgroup.closure {v₁, v₂} := by
      rw [hcl]
      exact AddSubgroup.mem_top v
    rw [AddSubgroup.mem_closure_pair] at this
    rcases this with ⟨m, n, rfl⟩
    have : MulActionHomClass (Module.End (ZMod p) (Additive P)) ℤ (Additive P) (Additive P) := {map_smulₛₗ := LinearMap.map_smul_of_tower}
    rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, hβ₁'1, hβ₁'2, hβ₂'1, hβ₂'2, he]
  have : Nat.card B = Nat.card (Set.range f) := by exact Eq.symm (Nat.card_range_of_injective this)
  rw [this]
  have : Nat.card L = q ^ 2 := by
    have : Finset.card {x : ZMod p | x ^ q = 1} = q := by
      have : Finset.card {x : ZMod p | x ^ q = 1} = Nat.card ({x : ZMod p | x ^ q = 1} : Finset (ZMod p)) := by rw [Nat.card_eq_finsetCard {x | x ^ q = 1}]
      rw [this]
      have : Nat.card ({x : ZMod p | x ^ q = 1} : Finset (ZMod p)) = Nat.card {x : ZMod p | x ^ q = 1} := by
        let f : ({x : ZMod p | x ^ q = 1} : Finset (ZMod p)) → {x : ZMod p | x ^ q = 1} := fun x' ↦ ⟨x'.val, by
          have := x'.prop
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this⟩
        refine Nat.card_eq_of_bijective f ?_
        constructor
        · intro x y hxy
          have : (f x).val = (f y).val := by rw [hxy]
          exact SetLike.coe_eq_coe.mp this
        · intro x
          use ⟨x.val, by
            have := Set.mem_setOf_eq ▸ x.prop
            simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
            exact this⟩
      rw [this]
      have : NeZero (p - 1) := by
        suffices h : p - 1 ≠ 0 by exact {out := h}
        have := Nat.Prime.one_lt factp.1
        omega
      have : HasEnoughRootsOfUnity (ZMod p) q := HasEnoughRootsOfUnity.of_dvd (ZMod p) (lemma_2_7_a hne hp hq hi)
      let f : rootsOfUnity q (ZMod p) → {x : ZMod p | x ^ q = 1}  := fun x' ↦ ⟨x'.val.val, by
        have : x'.val ∈ {ζ | ζ ^ q = 1} := Set.mem_setOf_eq ▸ Subgroup.mem_carrier.mpr x'.prop
        have : (x'.val ^ q).val = (1 : (ZMod p)ˣ).val := by rw [this]
        exact this⟩
      have : Function.Bijective f := by
        constructor
        · intro x y hxy
          have : (f x).val = (f y).val := by rw [hxy]
          have : x.val = y.val := Units.ext_iff.mpr this
          exact SetLike.coe_eq_coe.mp this
        · intro x
          let y : (rootsOfUnity q (ZMod p)) := ⟨Units.ofPowEqOne x.val q x.prop (Nat.Prime.ne_zero factq.1), by simp only [Set.mem_setOf_eq, mem_rootsOfUnity, Units.pow_ofPowEqOne]⟩
          use y
          have : y.val.val = x.val := by
            have : (Units.ofPowEqOne x.val q x.prop (Nat.Prime.ne_zero factq.1)).val = x.val := by
              simp only [Set.mem_setOf_eq, Units.val_ofPowEqOne]
            exact this
          exact SetCoe.ext this
      have : Nat.card (rootsOfUnity q (ZMod p)) = Nat.card {x : ZMod p | x ^ q = 1} := Nat.card_eq_of_bijective f this
      rw [← this]
      have := HasEnoughRootsOfUnity.natCard_rootsOfUnity (ZMod p) q
      rw [this]
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Set.toFinset_setOf,
      Finset.card_product, this, pow_two]
  rw [← this]
  have hf : Finite L := by
    apply Nat.finite_of_card_ne_zero
    rw [this]
    exact Ne.symm (NeZero.ne' (q ^ 2))
  have : Set.range f ⊆ L := by
    intro l hl
    rcases hl with ⟨β', hβ'⟩
    rw [← hβ']
    rcases hap β' with ⟨_, _, hβ'e1, hβ'e2⟩
    exact ⟨hβ'e1, hβ'e2⟩
  exact Nat.card_mono hf this

public theorem lemma_2_7_b
    {p q : ℕ} [factp : Fact p.Prime] [factq : Fact q.Prime] (hne : p ≠ q)
    {P Q : Type*} [Group P] [Group Q] [IsElementaryAbelian p P] [IsElementaryAbelian q Q]
    (hp : Nat.card P = p ^ 2) (hq : Nat.card Q = q ^ 2)
    (i : Q →* MulAut P) (hi : Function.Injective i) :
    ∃ α : Q, ∃ r : ℕ, α ≠ 1 ∧ ∀ x : P, (i α) x = x ^ r ∧ r ^ q ≡ 1 [MOD p] ∧ ¬ r ≡ 1 [MOD p] := by
  have : q ∣ p - 1 := lemma_2_7_a hne hp hq hi
  have : ∃ e : ZMod p, e ^ q = 1 ∧ e ≠ 1 := by
    have := (isCyclic_iff_exists_orderOf_eq_natCard (α := (ZMod p)ˣ)).mp inferInstance
    rcases this with ⟨g, hg⟩
    let k := (p - 1) / q
    have hm : k * q = p - 1 := Nat.div_mul_cancel this
    have hdvd : k ∣ (p - 1) := Nat.div_dvd_of_dvd this
    have hn0 : k ≠ 0 := by
      unfold k
      apply Nat.div_ne_zero_iff.mpr ⟨Nat.Prime.ne_zero factq.1, Nat.le_of_dvd ?_ this⟩
      rw [tsub_pos_iff_lt]
      exact Nat.Prime.one_lt factp.1
    have hord : orderOf (g ^ k) = q := by
      rw [← ZMod.card_units, Fintype.card_eq_nat_card, ← hg] at hdvd
      rw [orderOf_pow_of_dvd hn0 hdvd]
      rw [hg, Nat.card_eq_fintype_card, ZMod.card_units]
      exact (Nat.eq_div_of_mul_eq_right hn0 hm).symm
    use g ^ k
    constructor
    · rw [← pow_mul]
      have : g.val ^ (k * q) = (g ^ (k * q)).val := rfl
      rw [this, pow_mul, ← hord, pow_orderOf_eq_one]
      rfl
    · have : g.val ^ k = (g ^ k).val := rfl
      rw [this]
      by_contra
      rw [Units.val_eq_one.mp this] at hord
      rw [orderOf_one] at hord
      exact Nat.Prime.ne_one (factq.1) hord.symm
  rcases lemma_2_7_main_2 hne hp hq hi with ⟨v₁, v₂, heq, hcl, hv₁, hv₂⟩
  rcases this with ⟨e, he1, he2⟩
  have : e • (1 : Module.End (ZMod p) (Additive P)) ∈ {β |
    ∃ l₁ l₂ : ZMod p, β v₁ = l₁ • v₁ ∧ β v₂ = l₂ • v₂ ∧ l₁ ^ q = 1 ∧ l₂ ^ q = 1} := by
    simp only [exists_and_left, Set.mem_setOf_eq, LinearMap.smul_apply, Module.End.one_apply]
    use e
    exact ⟨rfl, by use e⟩
  rw [← heq] at this
  rcases this with ⟨α, hα⟩
  use α, e.val
  have hap : Additive.ofMul ((i α) (Additive.toMul v₁)) = (e • (1 : Module.End (ZMod p) (Additive P))) v₁ := by
      rw [← hα]
      rfl
  have hap2 : Additive.ofMul ((i α) (Additive.toMul v₂)) = (e • (1 : Module.End (ZMod p) (Additive P))) v₂ := by
      rw [← hα]
      rfl
  constructor
  · by_contra h
    rw [h] at hap
    simp only [map_one, MulAut.one_apply, ofMul_toMul, LinearMap.smul_apply, Module.End.one_apply] at hap
    nth_rw 1 [← sub_left_inj (a := e • v₁), sub_self, ← one_smul (M := ZMod p) v₁, ← sub_smul, smul_eq_zero] at hap
    rcases hap with h | h
    · rw [← add_left_inj (a := e), sub_add, sub_self, sub_zero, zero_add] at h
      exact he2 h.symm
    · exact hv₁ h
  intro x
  constructor
  · suffices h : Additive.ofMul ((i α) (Additive.toMul (Additive.ofMul x))) = Additive.ofMul (x ^ e.val) by
      have : Additive.ofMul (Additive.ofMul ((i α) (Additive.toMul (Additive.ofMul x)))) = Additive.ofMul (Additive.ofMul (x ^ e.val)) := by exact Equiv.Perm.congr_arg h
      simp only [toMul_ofMul] at this
      exact this
    set v := Additive.ofMul x
    have : v ∈ AddSubgroup.closure {v₁, v₂} := by
      rw [hcl]
      exact AddSubgroup.mem_top v
    rw [AddSubgroup.mem_closure_pair] at this
    rcases this with ⟨m, n, hv⟩
    have : MulActionHomClass (Module.End (ZMod p) (Additive P)) ℤ (Additive P) (Additive P) := {map_smulₛₗ := LinearMap.map_smul_of_tower}
    have (v : Additive P) (m : ℤ) : Additive.ofMul ((i α) (Additive.toMul (m • v))) = m • Additive.ofMul ((i α) (Additive.toMul v)) := by
      simp only [toMul_zsmul, map_zpow, ofMul_zpow]
    rw [← hv, toMul_add, map_mul, ofMul_mul, this, this, hap, hap2, ← map_smul, ← map_smul, ← map_add, hv]
    simp only [LinearMap.smul_apply, Module.End.one_apply, ofMul_pow, v]
    nth_rw 1 [← ZMod.natCast_zmod_val e, Nat.cast_smul_eq_nsmul]
  constructor
  have (n : ℕ) : e.val ^ n ≡ (e ^ n).val [MOD p]:= by
      induction n with
      | zero => rw [pow_zero, pow_zero, ZMod.val_one]
      | succ n hn =>
        have := @Nat.ModEq.mul_right p _ _ e.val hn
        have hval (e : ZMod p) := @Nat.mod_eq_of_lt e.val p (ZMod.val_lt e)
        have : e.val ^ n * e.val % p = (e ^ n).val * e.val % p := this
        rw [← pow_succ, ← ZMod.val_mul, ← pow_succ, ← hval (e ^ (n + 1))] at this
        exact this
  · have := this q
    rw [he1, ZMod.val_one] at this
    exact this
  · contrapose he2
    have h : 1 < p := Nat.Prime.one_lt factp.1
    have h' : e.val % p = 1 % p := he2
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (ZMod.val_lt e), ZMod.val_eq_one h] at h'
    exact h'
