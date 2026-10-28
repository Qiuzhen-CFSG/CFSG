module
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.Tactic

/-!
# Three conjugate involution subgroups

Suppose three subgroups of order two generate a group and are permuted by
conjugation according to a surjective action on three points. If each subgroup
fixes its own point and exchanges the other two, its unique involution
conjugates the other two involutions to one another. The resulting braid
relation bounds the generated group by the dihedral group of order six;
surjectivity makes this bound exact.

This is the quotient calculation in Goldschmidt, *Automorphisms of trivalent
graphs* (1980), final paragraph of (6.12), printed p.406.
-/

public section
namespace Theory.GroupTheory.ThreeConjugateInvolutionSubgroups
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An equivariant family of three transposition subgroups generates exactly S₃. -/
theorem card_eq_six (P : Fin 3 → Subgroup G)
    (hcard : ∀ i, Nat.card (P i) = 2) (hgen : iSup P = ⊤)
    (ρ : G →* Equiv.Perm (Fin 3)) (hsurj : Function.Surjective ρ)
    (hconj : ∀ g i, (P i).map (MulAut.conj g).toMonoidHom = P (ρ g i))
    (htrans : ∀ i j k, i ≠ j → i ≠ k → ∃ g ∈ P i, ρ g j = k) :
    Nat.card G = 6 := by
  classical
  have hex (i : Fin 3) := (Nat.card_eq_two_iff' (1 : P i)).mp (hcard i)
  choose a ha huniq using hex
  let u (i : Fin 3) : G := a i
  have hne (i : Fin 3) : u i ≠ 1 := fun he => ha i (Subtype.ext he)
  have hu (i : Fin 3) : u i ∈ P i := (a i).property
  have hsquare (i : Fin 3) : u i ^ 2 = 1 := by
    have hh : a i ^ 2 = 1 := by rw [← hcard i]; exact pow_card_eq_one'
    exact congrArg (fun x : P i => (x : G)) hh
  have heq (i : Fin 3) {x : G} (hx : x ∈ P i) (hx1 : x ≠ 1) : x = u i :=
    congrArg Subtype.val (huniq i ⟨x, hx⟩ (fun he => hx1 (congrArg Subtype.val he)))
  have hswap (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ρ (u i) j = k := by
    obtain ⟨g, hg, he⟩ := htrans i j k hij hik
    have hg1 : g ≠ 1 := by
      intro hg1
      rw [hg1, map_one] at he
      exact hjk he
    rwa [heq i hg hg1] at he
  have hc (i j : Fin 3) : u i * u j * (u i)⁻¹ = u (ρ (u i) j) := by
    apply heq
    · rw [← hconj]
      exact mem_map.mpr ⟨u j, hu j, rfl⟩
    · intro he
      apply hne j
      exact (MulAut.conj (u i)).injective (by simpa using he)
  have hi (i : Fin 3) : (u i)⁻¹ = u i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare i)
  have hab : u 0 * u 1 * u 0 = u 2 := by
    simpa only [hi, hswap 0 1 2 (by decide) (by decide) (by decide)] using hc 0 1
  have hba : u 1 * u 0 * u 1 = u 2 := by
    simpa only [hi, hswap 1 0 2 (by decide) (by decide) (by decide)] using hc 1 0
  have hcube : (u 1 * u 0) ^ 3 = 1 := by
    calc
      (u 1 * u 0) ^ 3 = (u 1 * u 0 * u 1) * (u 0 * u 1 * u 0) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = u 2 * u 2 := by rw [hab, hba]
      _ = 1 := by simpa only [pow_two] using hsquare 2
  have hP (i : Fin 3) : P i = zpowers (u i) := by
    apply le_antisymm
    · intro g hg
      by_cases hg1 : g = 1
      · exact hg1 ▸ one_mem _
      · rw [heq i hg hg1]
        exact mem_zpowers _
    · exact zpowers_le.mpr (hu i)
  let K := closure ({u 0, u 1} : Set G)
  have hm0 : u 0 ∈ K := subset_closure (by simp)
  have hm1 : u 1 ∈ K := subset_closure (by simp)
  have hK : K = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply iSup_le
    intro i
    rw [hP]
    apply zpowers_le.mpr
    fin_cases i
    · exact hm0
    · exact hm1
    · change u 2 ∈ K
      rw [← hab]
      exact K.mul_mem (K.mul_mem hm0 hm1) hm0
  have hbound := (closure_pair_finite_card_le_of_involutions
    (by decide : 0 < 3) (u 0) (u 1) (hsquare 0) (hsquare 1) hcube).2
  change Nat.card K ≤ 2 * 3 at hbound
  rw [hK, card_top] at hbound
  have hlower := Nat.card_le_card_of_surjective ρ hsurj
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [hperm] at hlower
  omega

end Theory.GroupTheory.ThreeConjugateInvolutionSubgroups
