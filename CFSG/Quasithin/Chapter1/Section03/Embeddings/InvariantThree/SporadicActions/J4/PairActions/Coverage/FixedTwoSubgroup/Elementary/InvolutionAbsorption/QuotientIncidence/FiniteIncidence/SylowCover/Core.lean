module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
public import Theory.GroupTheory.SubgroupEnumeration
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder.Packed
public import Mathlib.Data.Sym.Sym2

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
open FiniteIncidence
open scoped Sym2
/-!
# Counting certificate for the fixed Sylow double cosets

The subgroup fixes the unordered row pair {2148, 2163}. Distinct images of
this pair separate right cosets. A forest rooted at the published words
constructs coset representatives inside their double cosets. The certified
ambient order then turns a 256-element subgroup lower bound and 10395
distinct images into exact subgroup order and exhaustive coverage.

This is the finite counting step for the Proposition 1.3.4 J₄ case; the fixed
words and their source attribution are in the imported Words module.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover
attribute [local irreducible] Janko4.modelGroup quotientSubgroup baseSubgroup representative
abbrev A := quotientSubgroup
abbrev Pair := Sym2 Row

def pairRight (p : Pair) (g : A) : Pair := Sym2.map (fun v => right v g.val) p

theorem pairRight_one (p : Pair) : pairRight p 1 = p := by
  simp [pairRight, right_one, Sym2.map_id']

theorem pairRight_mul (p : Pair) (g h : A) :
    pairRight p (g * h) = pairRight (pairRight p g) h := by
  simp only [pairRight, Sym2.map_map]
  exact congrArg (fun f => Sym2.map f p) (funext (fun v => right_mul v g.val h.val))

def seed : Pair := s(row 2148, row 2163)

def fixer : Subgroup A where
  carrier := {g | pairRight seed g = seed}
  one_mem' := pairRight_one seed
  mul_mem' := by
    intro a b ha hb
    change pairRight seed (a * b) = seed
    rw [pairRight_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change pairRight seed a⁻¹ = seed
    have h := congrArg (fun p => pairRight p a⁻¹) ha
    simpa only [← pairRight_mul, mul_inv_cancel, pairRight_one] using h.symm

theorem factor_injective {n : ℕ} (rep : Fin n → A)
    (hi : Function.Injective (fun i => pairRight seed (rep i)))
    (hf : baseSubgroup ≤ fixer) :
    Function.Injective (fun p : Fin n × baseSubgroup => p.2.val * rep p.1) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hij : i = j := by
    apply hi
    have hv := congrArg (pairRight seed) h
    simpa only [pairRight_mul, show pairRight seed a.val = seed from hf a.property,
      show pairRight seed b.val = seed from hf b.property] using hv
  subst j
  have hab : a = b := Subtype.ext (mul_right_cancel h)
  subst b
  rfl

theorem count_and_cover (lo : 256 ≤ Nat.card baseSubgroup)
    (hf : baseSubgroup ≤ fixer)
    (rep : Fin 10395 → A)
    (hi : Function.Injective (fun i => pairRight seed (rep i)))
    (hd : ∀ i, ∃ j b, b ∈ baseSubgroup ∧ rep i = representative j * b) :
    Nat.card baseSubgroup = 256 ∧
      Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover baseSubgroup representative := by
  let f : Fin 10395 × baseSubgroup → A := fun p => p.2.val * rep p.1
  have hinj : Function.Injective f := factor_injective rep hi hf
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_fin, involutionMatrixQuotient_card] at hcard
  have heq : Nat.card baseSubgroup = 256 := by omega
  have hsurj := (hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_fin, heq, involutionMatrixQuotient_card])).2
  refine ⟨heq, fun x => ?_⟩
  obtain ⟨⟨i,a⟩, ha⟩ := hsurj x
  obtain ⟨j,b,hb,hr⟩ := hd i
  exact ⟨j,a.val,b,a.property,hb,by simpa only [f, hr, mul_assoc] using ha.symm⟩

abbrev Code := BitVec 12 × BitVec 12

def point (p : Code) : Pair := s(row p.1, row p.2)

def key (p : Code) : ℕ := p.1.toNat + 4096 * p.2.toNat

theorem points_injective {n : ℕ} (codes : Fin n → Code)
    (hs : ∀ i, (codes i).1.toNat ≤ (codes i).2.toNat)
    (hi : Function.Injective (fun i => key (codes i))) :
    Function.Injective (fun i => point (codes i)) := by
  intro i j h
  apply hi
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · simp only [key, row_injective h1, row_injective h2]
  · have h1 := congrArg BitVec.toNat (row_injective h1)
    have h2 := congrArg BitVec.toNat (row_injective h2)
    have hsi := hs i
    have hsj := hs j
    dsimp [key]
    omega

def Step (p q : Code) (rows : Vector ℕ 12) : Prop :=
  (packedRow p.1.toNat rows = q.1.toNat ∧ packedRow p.2.toNat rows = q.2.toNat) ∨
  (packedRow p.1.toNat rows = q.2.toNat ∧ packedRow p.2.toNat rows = q.1.toNat)

instance (p q : Code) (rows : Vector ℕ 12) : Decidable (Step p q rows) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

theorem step_sound (p q : Code) (g : A) (rows : Vector ℕ 12)
    (hg : g.val.val = quotientDecode rows) (h : Step p q rows) :
    pairRight (point p) g = point q := by
  change s(Matrix.vecMul (row p.1) g.val.val,
    Matrix.vecMul (row p.2) g.val.val) = s(row q.1, row q.2)
  rw [hg]
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [vecMul_eq_of_packed _ _ _ h1, vecMul_eq_of_packed _ _ _ h2]
  · rw [vecMul_eq_of_packed _ _ _ h1, vecMul_eq_of_packed _ _ _ h2]
    exact Sym2.eq_swap

theorem orbit_lower {n : ℕ} [NeZero n] (pts : Fin n → Pair)
    (parent : Fin n → Fin n) (letter : Fin n → Fin 4)
    (hlt : ∀ i, i ≠ 0 → parent i < i)
    (hedge : ∀ i, i ≠ 0 → pairRight (pts (parent i)) (sylowGenerator (letter i)) = pts i)
    (hinj : Function.Injective pts) : n ≤ Nat.card baseSubgroup := by
  have reach : ∀ i, ∃ g : baseSubgroup, pairRight (pts 0) g.val = pts i := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      by_cases hi : i = 0
      · subst i
        exact ⟨1, pairRight_one _⟩
      · obtain ⟨g,hg⟩ := ih (parent i) (hlt i hi)
        refine ⟨⟨g.val * sylowGenerator (letter i),
          baseSubgroup.mul_mem g.property (sylowGenerator_mem _)⟩, ?_⟩
        change pairRight (pts 0) (g.val * sylowGenerator (letter i)) = pts i
        rw [pairRight_mul, hg, hedge i hi]
  classical
  choose rep hrep using reach
  have hr : Function.Injective rep := by
    intro i j h
    apply hinj
    rw [← hrep i, ← hrep j, h]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective rep hr

theorem forest_reachable {n : ℕ} (pts : Fin n → Pair)
    (parent : Fin n → Fin n) (letter : Fin n → Fin 4) (root : Fin n → Fin 110)
    (hroot : ∀ i, ¬parent i < i → pairRight seed (representative (root i)) = pts i)
    (hedge : ∀ i, parent i < i →
      pairRight (pts (parent i)) (sylowGenerator (letter i)) = pts i) :
    ∀ i, ∃ j b, b ∈ baseSubgroup ∧ pairRight seed (representative j * b) = pts i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : parent i < i
    · obtain ⟨j,b,hb,hp⟩ := ih (parent i) hi
      refine ⟨j,b * sylowGenerator (letter i),
        baseSubgroup.mul_mem hb (sylowGenerator_mem _), ?_⟩
      rw [← mul_assoc, pairRight_mul, hp, hedge i hi]
    · exact ⟨root i, 1, baseSubgroup.one_mem, by rw [mul_one]; exact hroot i hi⟩

theorem count_and_cover_of_forest
    (lo : 256 ≤ Nat.card baseSubgroup) (hf : baseSubgroup ≤ fixer)
    (pts : Fin 10395 → Pair) (hinj : Function.Injective pts)
    (reach : ∀ i, ∃ j b, b ∈ baseSubgroup ∧
      pairRight seed (representative j * b) = pts i) :
    Nat.card baseSubgroup = 256 ∧
      Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover baseSubgroup representative := by
  classical
  choose j b hb hpoint using reach
  apply count_and_cover lo hf (fun i => representative (j i) * b i)
  · intro i k h
    apply hinj
    simpa only [hpoint] using h
  · intro i
    exact ⟨j i, b i, hb i, rfl⟩

theorem forall_fin_of_range {n : ℕ} [NeZero n]
    (P : Fin n → Prop) [DecidablePred P]
    (h : (List.range n).all (fun i => decide (P (Fin.ofNat n i))) = true) : ∀ i, P i := by
  intro i
  have hi := of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simpa only [Fin.ofNat_val_eq_self] using hi

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover
