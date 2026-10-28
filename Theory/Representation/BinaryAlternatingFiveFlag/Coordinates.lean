module
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.BinaryPermutation.FiveCentralizerGeometry
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The Sylow-invariant hyperplane of the binary five-point core

The Klein four group regular on the first four letters fixes a unique
hyperplane of the even-weight core: the vectors vanishing at the fifth letter.
Indeed the orbit of any vector outside that hyperplane is a basis. The point
stabilizer A₄ preserves this hyperplane, its fixed line, and acts irreducibly
on the quotient by that line. All finite checks involve only five letters
and sixteen vectors.

Source: Aschbacher–Smith, 13.5.7(b), 13.5.14, and the module conventions of B.3.
-/
@[expose] public section
namespace BinaryPermutation.AlternatingFiveFlag
open Subgroup FiveCentralizerGeometry
abbrev Perm := Equiv.Perm (Fin 5)
abbrev rho := coreRepresentation (Fin 5)

instance spaceDecidable : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
instance spaceFintype : Fintype Space := Subtype.fintype _

def k₀ : Perm := Equiv.swap 0 1 * Equiv.swap 2 3
def k₁ : Perm := Equiv.swap 0 2 * Equiv.swap 1 3

def four : Subgroup Perm where
  carrier := {g | g = 1 ∨ g = k₀ ∨ g = k₁ ∨ g = k₀ * k₁}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro g h (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide +kernel
  inv_mem' := by
    rintro g (rfl | rfl | rfl | rfl) <;> decide +kernel

instance : DecidablePred (· ∈ four) := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
instance : Fintype four := Subtype.fintype _

theorem four_card : Nat.card four = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem four_isPGroup : IsPGroup 2 four := IsPGroup.of_card (n := 2) four_card

theorem four_even : four ≤ alternatingGroup (Fin 5) := by
  rintro g (rfl | rfl | rfl | rfl) <;> rw [Equiv.Perm.mem_alternatingGroup] <;> decide +kernel

theorem fixes_z_iff (g : Perm) : rho g z = z ↔ g 4 = 4 := by
  have h : ∀ g : Perm, rho g z = z ↔ g 4 = 4 := by decide +kernel
  exact h g

private theorem conjugate_four_mem (g : Perm) (hg : g 4 = 4) (k : Perm) (hk : k ∈ four) :
    g*k*g⁻¹ ∈ four := by
  have h₀ : ∀ g : Perm, g 4=4 → g*k₀*g⁻¹ ∈ four := by decide +kernel
  have h₁ : ∀ g : Perm, g 4=4 → g*k₁*g⁻¹ ∈ four := by decide +kernel
  rcases hk with rfl|rfl|rfl|rfl
  · simp
  · exact h₀ g hg
  · exact h₁ g hg
  · have hh := four.mul_mem (h₀ g hg) (h₁ g hg)
    convert hh using 1
    group

theorem normalizes_four_of_fixes (g : Perm) (hg : g 4 = 4) : g ∈ normalizer (four : Set Perm) := by
  intro k
  constructor
  · exact conjugate_four_mem g hg k
  · intro hk
    have hi : g⁻¹ 4=4 := g.symm_apply_eq.mpr hg.symm
    have hh := conjugate_four_mem g⁻¹ hi (g*k*g⁻¹) hk
    have he : g⁻¹*(g*k*g⁻¹)*g=k := by group
    rw [inv_inv,he] at hh
    exact hh

/-- The regular four group lies in every Sylow fixing the standard line. -/
theorem four_le_sylow (H : Subgroup Perm) (hH : alternatingGroup (Fin 5) ≤ H)
    (P : Sylow 2 H) (hfix : ∀ p : H, p ∈ P → rho p.val z = z) :
    four ≤ (P : Subgroup H).map H.subtype := by
  let K := four.subgroupOf H
  have hKH : four ≤ H := four_even.trans hH
  have hn : (P : Subgroup H) ≤ normalizer (K : Set H) := by
    intro p hp k
    exact normalizes_four_of_fixes p.val ((fixes_z_iff p.val).mp (hfix p hp)) k.val
  have hmax := P.is_maximal' (four_isPGroup.comap_subtype.to_sup_of_normal_left' P.isPGroup' hn)
    (show (P : Subgroup H) ≤ K ⊔ P from le_sup_right)
  have hk : K ≤ (P : Subgroup H) := le_sup_left.trans hmax.le
  have hm := map_mono (f := H.subtype) hk
  rwa [map_subgroupOf_eq_of_le hKH] at hm

def three : Subgroup (Multiplicative Space) where
  carrier := {x | x.toAdd.val 4 = 0}
  one_mem' := rfl
  mul_mem' {x y} hx hy := by change x.toAdd.val 4 + y.toAdd.val 4 = 0; rw [hx,hy,add_zero]
  inv_mem' {x} hx := by change -x.toAdd.val 4 = 0; rw [hx,neg_zero]
instance : DecidablePred (· ∈ three) := fun _ => inferInstanceAs (Decidable (_ = _))
instance : Fintype three := Subtype.fintype _

theorem three_card : Nat.card three = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem orbit_basis : ∀ x y : Space, x.val 4 ≠ 0 →
    ∃ a b c d : Bool, y = (if a then x else 0) + (if b then rho k₀ x else 0) +
      (if c then rho k₁ x else 0) + (if d then rho (k₀*k₁) x else 0) := by decide +kernel

/-- A subgroup of order eight invariant under the regular four group is the standard hyperplane. -/
theorem three_eq_of_card_invariant (U : Subgroup (Multiplicative Space))
    (hc : Nat.card U = 8)
    (hi : ∀ g ∈ four, ∀ x ∈ U, Multiplicative.ofAdd (rho g x.toAdd) ∈ U) : U = three := by
  have hle : U ≤ three := by
    intro x hx
    by_contra hn
    have ht : U = ⊤ := by
      apply eq_top_iff.mpr
      intro y _
      obtain ⟨a,b,c,d,he⟩ := orbit_basis x.toAdd y.toAdd hn
      have h₀ := hi k₀ (Or.inr (Or.inl rfl)) x hx
      have h₁ := hi k₁ (Or.inr (Or.inr (Or.inl rfl))) x hx
      have h₂ := hi (k₀*k₁) (Or.inr (Or.inr (Or.inr rfl))) x hx
      have hif (b : Bool) (v : Multiplicative Space) (hv : v ∈ U) :
          Multiplicative.ofAdd (if b then v.toAdd else 0) ∈ U := by
        cases b
        · exact U.one_mem
        · exact hv
      change Multiplicative.ofAdd y.toAdd ∈ U
      rw [he, ofAdd_add, ofAdd_add, ofAdd_add]
      exact U.mul_mem (U.mul_mem (U.mul_mem (hif a x hx) (hif b _ h₀)) (hif c _ h₁)) (hif d _ h₂)
    have hc16 : Nat.card (Multiplicative Space) = 16 := by rw [Nat.card_eq_fintype_card]; decide +kernel
    rw [ht,card_top,hc16] at hc
    omega
  exact eq_of_le_of_card_ge hle (by rw [hc,three_card])

end BinaryPermutation.AlternatingFiveFlag
