module

public import Theory.GroupTheory.WordSubgroup
public import Mathlib.Data.Fin.VecNotation

/-!
# Lower bounds from distinct stabilizer cosets

A family of permutations in H with distinct images of a point gives disjoint
left cosets of every subgroup K fixing that point. Multiplication therefore
embeds the product of the family and K in H. This is the lower-bound half of
the orbit--stabilizer argument, used by the concrete star-group certificate.
-/

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
open Theory.GroupTheory

-- Lower-bound half of the transversal argument, without a Schreier closure check.
theorem card_mul_le {V : Type*} [Fintype V] [DecidableEq V]
    (H K : Subgroup (Equiv.Perm V)) (hle : K ≤ H)
    {m : ℕ} (rep : Fin m → Equiv.Perm V) (base : V)
    (hmem : ∀ i, rep i ∈ H)
    (hinj : Function.Injective (fun i => rep i base))
    (hfix : ∀ k : K, (k : Equiv.Perm V) base = base) :
    m * Nat.card K ≤ Nat.card H := by
  let f : Fin m × K → H := fun x =>
    ⟨rep x.1 * (x.2 : Equiv.Perm V), H.mul_mem (hmem x.1) (hle x.2.property)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, k⟩ ⟨j, l⟩ h
    have hp := congrArg Subtype.val h
    change rep i * (k : Equiv.Perm V) = rep j * (l : Equiv.Perm V) at hp
    have hi : i = j := by
      apply hinj
      have hb := congrArg (fun p : Equiv.Perm V => p base) hp
      simpa only [Equiv.Perm.mul_apply, hfix] using hb
    subst j
    have hk : k = l := Subtype.ext (mul_left_cancel hp)
    subst l
    rfl
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf


def generated {n : ℕ} (gen : Fin n → Equiv.Perm (Fin 24)) :=
  Subgroup.closure (Set.range gen)

theorem word_mem {n : ℕ} (gen : Fin n → Equiv.Perm (Fin 24))
    (H : Subgroup (Equiv.Perm (Fin 24))) (h : ∀ i, gen i ∈ H) (w : List (Fin n)) :
    evalWord gen w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (h i) ih

theorem generated_le {n : ℕ} (gen : Fin n → Equiv.Perm (Fin 24))
    (H : Subgroup (Equiv.Perm (Fin 24))) (h : ∀ i, gen i ∈ H) : generated gen ≤ H := by
  apply (Subgroup.closure_le H).mpr
  rintro _ ⟨i, rfl⟩
  exact h i

theorem gen_mem {n : ℕ} (gen : Fin n → Equiv.Perm (Fin 24)) (i : Fin n) :
    gen i ∈ generated gen := Subgroup.subset_closure ⟨i, rfl⟩

theorem generated_fix {n : ℕ} (gen : Fin n → Equiv.Perm (Fin 24)) (base : Fin 24)
    (h : ∀ i, gen i base = base) : ∀ k : generated gen, (k : Equiv.Perm (Fin 24)) base = base := by
  have hle : generated gen ≤ MulAction.stabilizer (Equiv.Perm (Fin 24)) base :=
    generated_le gen _ h
  intro k
  exact hle k.property

end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
