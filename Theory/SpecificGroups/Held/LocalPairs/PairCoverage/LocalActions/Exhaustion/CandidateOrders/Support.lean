module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.Contracts
public import Theory.GroupTheory.CyclicExtension
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.FinCases

/-!
# Soundness of finite cyclic-series certificates for the Held candidates

A power relation and conjugation relations bound the index of each step
of a finite cyclic series. Multiplying those bounds gives an upper bound.
For the lower bound we exhibit words distinguished by their actual action.
Every certificate used later is checked in the fixed ATLAS permutation carrier.
Source: the elementary cyclic-extension argument; candidate words from the
ATLAS max3/max4 programs and the retained LocalActions/source exploration.
-/

@[expose] public section

namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
variable {G : Type*} [Group G] [Finite G]
theorem collect (S : Set G) (a : G) (m : ℕ) (hm : 0 < m)
    (ha : a ^ m ∈ Subgroup.closure S)
    (hc : ∀ b ∈ S, a * b * a⁻¹ ∈ Subgroup.closure S)
    {x : G} (hx : x ∈ Subgroup.closure (insert a S)) :
    ∃ y ∈ Subgroup.closure S, ∃ i : Fin m, y * a ^ i.val = x := by
  have hconj : ∀ y ∈ Subgroup.closure S, a * y * a⁻¹ ∈ Subgroup.closure S := by
    have hle : Subgroup.closure S ≤
        (Subgroup.closure S).comap (MulAut.conj a).toMonoidHom :=
      (Subgroup.closure_le _).mpr hc
    exact hle
  change x ∈ (Subgroup.closure (insert a S)).toSubmonoid at hx
  rw [Subgroup.closure_toSubmonoid_of_finite] at hx
  induction hx using Submonoid.closure_induction_left with
  | one => exact ⟨1, (Subgroup.closure S).one_mem, ⟨0, hm⟩, by simp⟩
  | mul_left b hb x _ ih =>
    rcases ih with ⟨y, hy, i, rfl⟩
    rcases hb with rfl | hb
    · by_cases hi : i.val + 1 < m
      · refine ⟨b * y * b⁻¹, hconj y hy, ⟨i.val + 1, hi⟩, ?_⟩
        simp [pow_succ', mul_assoc]
      · have he : m = i.val + 1 := by omega
        refine ⟨(b * y * b⁻¹) * b ^ m,
          (Subgroup.closure S).mul_mem (hconj y hy) ha, ⟨0, hm⟩, ?_⟩
        simp [he, pow_succ', mul_assoc]
    · exact ⟨b * y, (Subgroup.closure S).mul_mem (Subgroup.subset_closure hb) hy,
        i, mul_assoc _ _ _⟩

theorem card_insert_le (S : Set G) (a : G) (m : ℕ) (hm : 0 < m)
    (ha : a ^ m ∈ Subgroup.closure S)
    (hc : ∀ b ∈ S, a * b * a⁻¹ ∈ Subgroup.closure S) :
    Nat.card (Subgroup.closure (insert a S)) ≤ Nat.card (Subgroup.closure S) * m := by
  let H := Subgroup.closure S
  let K := Subgroup.closure (insert a S)
  have hHK : H ≤ K := Subgroup.closure_mono (Set.subset_insert a S)
  let f : H × Fin m → K := fun p => ⟨p.1.val * a ^ p.2.val,
    K.mul_mem (hHK p.1.property) (K.pow_mem (Subgroup.subset_closure (Set.mem_insert a S)) _)⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y, hy, i, hi⟩ := collect S a m hm ha hc x.property
    exact ⟨(⟨y, hy⟩, i), Subtype.ext hi⟩
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_surjective f hf
end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate

namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
variable {G : Type*} [Group G] [Finite G]
def triangular : List (G × ℕ) → Prop
  | [] => True
  | (a, m) :: l => 0 < m ∧ a ^ m ∈ Subgroup.closure (Prod.fst '' {x | x ∈ l}) ∧
      (∀ b ∈ l, a * b.1 * a⁻¹ ∈ Subgroup.closure (Prod.fst '' {x | x ∈ l})) ∧ triangular l

theorem card_le (l : List (G × ℕ)) (h : triangular l) :
    Nat.card (Subgroup.closure (Prod.fst '' {x | x ∈ l})) ≤ (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨a, m⟩ := p
    obtain ⟨hm, ha, hc, ht⟩ := h
    have he : Prod.fst '' {x | x ∈ (a, m) :: l} =
        insert a (Prod.fst '' {x | x ∈ l}) := by
      ext x
      simp [eq_comm]
    rw [he]
    apply (card_insert_le _ a m hm ha ?_).trans
    · simpa [Nat.mul_comm] using Nat.mul_le_mul_right m (ih ht)
    · rintro _ ⟨b, hb, rfl⟩
      exact hc b hb

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
variable {G I : Type*} [Group G]
theorem triangular_cons_words (g : I → G) (r : I → ℕ) (a : I) (l : List I)
    (hm : 0 < r a) (sw : List I) (cw : I → List I)
    (hs : g a ^ r a = (sw.map g).prod)
    (hc : ∀ b ∈ l, g a * g b * (g a)⁻¹ = ((cw b).map g).prod)
    (hsupp : ∀ i ∈ sw, i ∈ l)
    (csupp : ∀ b ∈ l, ∀ i ∈ cw b, i ∈ l)
    (ht : triangular (l.map (fun p => (g p, r p)))) :
    triangular ((a :: l).map (fun p => (g p, r p))) := by
  refine ⟨hm, ?_, ?_, ht⟩
  · rw [hs]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure
      ⟨(g i,r i), List.mem_map.mpr ⟨i,hsupp i hi,rfl⟩,rfl⟩
  · intro b hb
    obtain ⟨b,hl,rfl⟩ := List.mem_map.mp hb
    rw [hc b hl]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure
      ⟨(g i,r i), List.mem_map.mpr ⟨i,csupp b hl i hi,rfl⟩,rfl⟩
end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate

namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
variable {G H I : Type*} [Group G] [Group H]

def evalSigned (g : I → G) (w : List (I × ℤ)) : G :=
  (w.map (fun t => g t.1 ^ t.2)).prod

theorem map_evalSigned (f : G →* H) (g : I → G) (w : List (I × ℤ)) :
    f (evalSigned g w) = evalSigned (fun i => f (g i)) w := by
  simp only [evalSigned, map_list_prod, List.map_map, Function.comp_def, map_zpow]

theorem evalSigned_mem (g : I → G) (w : List (I × ℤ)) (K : Subgroup G)
    (hg : ∀ i, g i ∈ K) : evalSigned g w ∈ K := by
  apply K.list_prod_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact K.zpow_mem (hg t.1) _

def checkFin (n : ℕ) (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i,h⟩ else false)

theorem allFin (n : ℕ) (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin n (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [i.isLt, dite_true, decide_eq_true_eq] using hi

theorem lower_bound {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (n : ℕ) (f : Fin n → G) (d : G → ℕ)
    (hf : ∀ i, f i ∈ K) (hd : ∀ i, d (f i) = i.val) : n ≤ Nat.card K := by
  let e : Fin n → K := fun i => ⟨f i, hf i⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    rw [← hd i, ← hd j]
    exact congrArg d (congrArg Subtype.val hij)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective e he

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
