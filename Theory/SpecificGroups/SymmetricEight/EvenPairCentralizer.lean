module

public import Theory.SpecificGroups.SymmetricEight.InvolutionActions
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Tactic

/-!
# The centralizer of the six-point alternating subgroup in S₈

Four explicit three-cycles in the alternating subgroup fixing 0 and 1
have distinct patterns of moved points on the other six points. A commuting
permutation must therefore fix all six. It is either the identity or (0 1).
The actual S₈ ≃ Aut(A₈) action transfers this bound to any compatibly marked
embedding. No classification of arbitrary A₆ embeddings is assumed here.

Source: the PSL₄(2) row in Aschbacher–Smith, 16.1.7(3e) and 16.3.5,
combined manuscript of 1 March 2004, printed pp.1172 and 1178–1179.
-/

@[expose] public section
open Subgroup Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricEight.EvenPairCentralizer
local notation "S" => Perm (Fin 8)
/-- Even permutations fixing the two marked points individually. -/
def evenPair : Subgroup S := alternatingGroup (Fin 8) ⊓
  (MulAction.stabilizer S (0 : Fin 8) ⊓ MulAction.stabilizer S (1 : Fin 8))
private def cycles : Fin 4 → S := ![swap 2 3 * swap 3 4, swap 2 5 * swap 5 6,
  swap 3 5 * swap 5 7, swap 4 6 * swap 6 7]
private theorem cycles_mem : ∀ j, cycles j ∈ evenPair := by
  simp only [evenPair, mem_inf, mem_alternatingGroup, MulAction.mem_stabilizer_iff]
  decide +kernel
private theorem distinguishes : ∀ x y : Fin 8, 2 ≤ x.val →
    (∀ j, (cycles j x = x ↔ cycles j y = y)) → x = y := by decide +kernel

private theorem centralizer_fixes (g : S) (hg : g ∈ centralizer (evenPair : Set S))
    (x : Fin 8) (hx : 2 ≤ x.val) : g x = x := by
  apply (distinguishes x (g x) hx ?_).symm
  intro j
  have hc := congrArg (fun p : S => p x)
    (mem_centralizer_iff.mp hg (cycles j) (cycles_mem j))
  change cycles j (g x) = g (cycles j x) at hc
  rw [hc, g.injective.eq_iff]

private theorem centralizer_two (g : S) (hg : g ∈ centralizer (evenPair : Set S)) :
    g = 1 ∨ g = swap 0 1 := by
  have hs : g.support ⊆ {0, 1} := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    have hxv : 2 ≤ x.val := by
      simp only [not_or] at hn
      have h0 : x.val ≠ 0 := fun h => hn.1 (Fin.ext h)
      have h1 : x.val ≠ 1 := fun h => hn.2 (Fin.ext h)
      omega
    exact (mem_support.mp hx) (centralizer_fixes g hg x hxv)
  by_cases he : g = 1
  · exact Or.inl he
  right
  have hc : g.support.card = 2 := by
    have hu := Finset.card_le_card hs
    have hl := two_le_card_support_of_ne_one he
    norm_num at hu
    omega
  obtain ⟨a, b, hab, rfl⟩ := card_support_eq_two.mp hc
  have ha := hs (by simp [support_swap hab] : a ∈ (swap a b).support)
  have hb := hs (by simp [support_swap hab] : b ∈ (swap a b).support)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · rfl
  · exact swap_comm _ _
  · exact (hab rfl).elim

/-- The full permutation centralizer has order at most two. -/
theorem centralizer_card_le_two : Nat.card (centralizer (evenPair : Set S)) ≤ 2 := by
  let f : centralizer (evenPair : Set S) → ({1, swap 0 1} : Set S) := fun g =>
    ⟨g.val, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff]
      using centralizer_two g.val g.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : ({1, swap 0 1} : Set S) => z.val) h
  have hc := Nat.card_le_card_of_injective f hf
  have ht : Nat.card ({1, swap 0 1} : Set S) = 2 := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_ofFinset]
    decide +kernel
  rwa [ht] at hc
open Theory.SpecificGroups.SymmetricEight.Involutions

variable {H : Type*} [Group H]
/-- Transport the bound to the full automorphism fixer of the marked subgroup. -/
theorem automorphismFixer_card_le_two (e : H ≃* alternatingGroup (Fin 8)) (P : Subgroup H)
    (hP : P.map ((alternatingGroup (Fin 8)).subtype.comp e.toMonoidHom) = evenPair) :
    Nat.card (fixingSubgroup (MulAut H) (P : Set H)) ≤ 2 := by
  let f : fixingSubgroup (MulAut H) (P : Set H) → centralizer (evenPair : Set S) :=
    fun a => ⟨automorphismPermutationEquiv e a.val, by
      rw [mem_centralizer_iff]
      intro y hy
      rw [← hP] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have ha := automorphismPermutationEquiv_action e a.val x
      have hfix : a.val x = x := a.property ⟨x, hx⟩
      rw [hfix] at ha
      exact eq_mul_inv_iff_mul_eq.mp ha⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext ((automorphismPermutationEquiv e).injective (congrArg Subtype.val h))
  exact (Nat.card_le_card_of_injective f hf).trans centralizer_card_le_two
end Theory.SpecificGroups.SymmetricEight.EvenPairCentralizer
