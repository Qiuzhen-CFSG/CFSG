module

public import Theory.GroupTheory.BinaryCollection
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Orders of subsequences of binary normal forms

Inserting zero bits embeds the binary words on a subsequence into the words
on the original sequence. Consequently uniqueness for the original sequence
implies uniqueness for every subsequence. If a subsequence is triangular,
collection supplies the reverse cardinal bound and its generated subgroup
has order two to the length of the subsequence.

This is the elementary polycyclic normal-form counting argument. Its concrete
consumer is the third-term order calculation for the J₄ Sylow presentation.
-/

public section

namespace Theory.GroupTheory.BinaryCollection
variable {G : Type*} [Group G]

private theorem embedding_of_sublist {l L : List G} (h : l.Sublist L) :
    ∃ f : ℕ → ℕ,
      (∀ n, n < 2 ^ l.length → f n < 2 ^ L.length) ∧
      (∀ n, product L (f n) = product l n) ∧
      (∀ n, n < 2 ^ l.length → ∀ m, m < 2 ^ l.length → f n = f m → n = m) := by
  induction h with
  | slnil =>
    refine ⟨id, ?_, ?_, ?_⟩
    · exact fun _ hn => hn
    · intro n; rfl
    · exact fun _ _ _ _ hn => hn
  | @cons l L a h ih =>
    obtain ⟨f, hb, hp, hi⟩ := ih
    refine ⟨fun n => 2 * f n, ?_, ?_, ?_⟩
    · intro n hn
      have := hb n hn
      simp only [List.length_cons, pow_succ]
      omega
    · intro n
      simpa [product] using hp n
    · intro n hn m hm he
      dsimp only at he
      exact hi n hn m hm (by omega)
  | @cons_cons l L a h ih =>
    obtain ⟨f, hb, hp, hi⟩ := ih
    have hd (n : ℕ) (hn : n < 2 ^ (a :: l).length) : n / 2 < 2 ^ l.length := by
      simp only [List.length_cons, pow_succ] at hn
      omega
    refine ⟨fun n => 2 * f (n / 2) + n % 2, ?_, ?_, ?_⟩
    · intro n hn
      have := hb (n / 2) (hd n hn)
      have := Nat.mod_lt n (by decide : 0 < 2)
      simp only [List.length_cons, pow_succ]
      omega
    · intro n
      have hm : (2 * f (n / 2) + n % 2) % 2 = n % 2 := by omega
      have hq : (2 * f (n / 2) + n % 2) / 2 = f (n / 2) := by omega
      simp only [product, hm, hq, hp]
    · intro n hn m hm he
      dsimp only at he
      have heq : f (n / 2) = f (m / 2) := by omega
      have := hi (n / 2) (hd n hn) (m / 2) (hd m hm) heq
      omega

/-- A subsequence inherits uniqueness of ascending binary forms. -/
theorem injective_product_of_sublist {l L : List G} (h : l.Sublist L)
    (hinj : Function.Injective (fun n : Fin (2 ^ L.length) => product L n.val)) :
    Function.Injective (fun n : Fin (2 ^ l.length) => product l n.val) := by
  obtain ⟨f, hb, hp, hi⟩ := embedding_of_sublist h
  intro n m he
  have h : (⟨f n.val, hb n.val n.isLt⟩ : Fin (2 ^ L.length)) =
      ⟨f m.val, hb m.val m.isLt⟩ := hinj (by simpa only [hp] using he)
  exact Fin.ext (hi n.val n.isLt m.val m.isLt (congrArg Fin.val h))

private theorem product_mem_closure (l : List G) (n : ℕ) :
    product l n ∈ Subgroup.closure {x | x ∈ l} := by
  induction l generalizing n with
  | nil => exact (Subgroup.closure _).one_mem
  | cons a l ih =>
    exact (Subgroup.closure _).mul_mem
      ((Subgroup.closure _).pow_mem (Subgroup.subset_closure (by simp)) _)
      ((Subgroup.closure_mono (by intro x hx; exact List.mem_cons_of_mem a hx)) (ih _))

/-- Triangularity and uniqueness give the order of the generated subgroup. -/
theorem card_closure_of_injective (l : List G) (ht : triangular l)
    (hinj : Function.Injective (fun n : Fin (2 ^ l.length) => product l n.val)) :
    Nat.card (Subgroup.closure {x | x ∈ l}) = 2 ^ l.length := by
  let f : Fin (2 ^ l.length) → Subgroup.closure {x | x ∈ l} :=
    fun n => ⟨product l n.val, product_mem_closure l n.val⟩
  have hf : Function.Bijective f := by
    constructor
    · intro n m h
      exact hinj (congrArg Subtype.val h)
    · intro x
      obtain ⟨n, hn, he⟩ := cover l ht x.val x.property
      exact ⟨⟨n, hn⟩, Subtype.ext he⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fin]

/-- A triangular subsequence of unique binary forms has the expected order. -/
theorem card_closure_of_sublist {l L : List G} (h : l.Sublist L) (ht : triangular l)
    (hinj : Function.Injective (fun n : Fin (2 ^ L.length) => product L n.val)) :
    Nat.card (Subgroup.closure {x | x ∈ l}) = 2 ^ l.length :=
  card_closure_of_injective l ht (injective_product_of_sublist h hinj)
end Theory.GroupTheory.BinaryCollection
