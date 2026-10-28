module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientModel
public import Mathlib.Data.Fintype.CardEmbedding
/-!
# Lower bounds from right-row orbit trees

For matrices acting on row vectors on the right, distinct images of a vector
separate the cosets `K * rep`. Multiplication embeds `Fin n × K` in `H`.
A rooted tree whose edges are generators in `H` constructs the representatives
without evaluating long matrix words. Applied to the literal max2 quotient
matrices, this supplies the lower-bound half of orbit--stabilizer.

The finite witnesses are attributed in `source/README.md`. No assertion that
the trees exhaust the orbits, or that the subgroups exhaust the stabilizers,
is needed for this lower bound.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientOrderCertificate
abbrev Row := Fin 12 → ZMod 2
abbrev U := QuotientMatrixˣ

def row (n : BitVec 12) : Row := fun j => if n.getLsbD j.val then 1 else 0

theorem row_injective : Function.Injective row := by
  intro a b hab
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := congrFun hab ⟨i, hi⟩
  change (if a.getLsbD i then (1 : ZMod 2) else 0) =
    (if b.getLsbD i then (1 : ZMod 2) else 0) at h
  cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp_all

def right (v : Row) (g : U) : Row := Matrix.vecMul v g.val

theorem right_one (v : Row) : right v 1 = v := Matrix.vecMul_one v

theorem right_mul (v : Row) (g h : U) :
    right v (g * h) = right (right v g) h := (Matrix.vecMul_vecMul v g.val h.val).symm

def stabilizer (v : Row) : Subgroup U where
  carrier := {g | right v g = v}
  one_mem' := right_one v
  mul_mem' := by
    intro g h hg hh
    change right v (g * h) = v
    rw [right_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change right v g⁻¹ = v
    have h := congrArg (fun v => right v g⁻¹) hg
    simpa only [← right_mul, mul_inv_cancel, right_one] using h.symm

theorem card_mul_le (H K : Subgroup U) (hKH : K ≤ H)
    {n : ℕ} (v : Row) (rep : Fin n → H)
    (hinj : Function.Injective (fun i => right v (rep i).val))
    (hfix : ∀ k : K, right v k.val = v) :
    n * Nat.card K ≤ Nat.card H := by
  let f : Fin n × K → H := fun p =>
    ⟨p.2.val * (rep p.1).val, H.mul_mem (hKH p.2.property) (rep p.1).property⟩
  have hf : Function.Injective f := by
    rintro ⟨i, k⟩ ⟨j, l⟩ h
    have hp := congrArg Subtype.val h
    change k.val * (rep i).val = l.val * (rep j).val at hp
    have hij : i = j := by
      apply hinj
      have hv := congrArg (right v) hp
      simpa only [right_mul, hfix] using hv
    subst j
    have hkl : k = l := Subtype.ext (mul_right_cancel hp)
    subst l
    rfl
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf

theorem tree_reachable {n k : ℕ} [NeZero n] (H : Subgroup U)
    (gen : Fin k → U) (hgen : ∀ j, gen j ∈ H)
    (point : Fin n → Row) (parent : Fin n → Fin n) (letter : Fin n → Fin k)
    (hlt : ∀ i, i ≠ 0 → parent i < i)
    (hedge : ∀ i, i ≠ 0 → right (point (parent i)) (gen (letter i)) = point i) :
    ∀ i, ∃ g : H, right (point 0) g.val = point i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · subst i
      exact ⟨1, right_one _⟩
    · obtain ⟨g, hg⟩ := ih (parent i) (hlt i hi)
      refine ⟨⟨g.val * gen (letter i), H.mul_mem g.property (hgen _)⟩, ?_⟩
      change right (point 0) (g.val * gen (letter i)) = point i
      rw [right_mul, hg, hedge i hi]

theorem tree_card_mul_le {n k : ℕ} [NeZero n] (H K : Subgroup U)
    (hKH : K ≤ H) (gen : Fin k → U) (hgen : ∀ j, gen j ∈ H)
    (point : Fin n → Row) (parent : Fin n → Fin n) (letter : Fin n → Fin k)
    (hlt : ∀ i, i ≠ 0 → parent i < i)
    (hedge : ∀ i, i ≠ 0 → right (point (parent i)) (gen (letter i)) = point i)
    (hinj : Function.Injective point)
    (hfix : ∀ g : K, right (point 0) g.val = point 0) :
    n * Nat.card K ≤ Nat.card H := by
  classical
  choose rep hrep using tree_reachable H gen hgen point parent letter hlt hedge
  apply card_mul_le H K hKH (point 0) rep _ hfix
  intro i j hij
  apply hinj
  simpa only [hrep] using hij
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientOrderCertificate
