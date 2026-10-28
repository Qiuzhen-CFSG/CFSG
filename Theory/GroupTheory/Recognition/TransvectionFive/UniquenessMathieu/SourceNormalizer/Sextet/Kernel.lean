module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Action
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-!
# The kernel of the exceptional six-point action

The first three exceptional four-groups form a direct sum. Enumerate the six
ordered bases in each of them, then test the remaining three four-groups.
A symmetry fixing all six four-groups and any nonzero vector is the identity.
Thus evaluation at 12 embeds the six-point kernel into a three-element set.
The certificates inspect only 216 choices, rather than all binary matrices.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4, p.218.
-/

public section

namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code)

private def bits (v : Fin 6 → Code) (x : Code) : Code :=
  (if x.getLsbD 0 then v 0 else 0) ^^^ (if x.getLsbD 1 then v 1 else 0) ^^^
  (if x.getLsbD 2 then v 2 else 0) ^^^ (if x.getLsbD 3 then v 3 else 0) ^^^
  (if x.getLsbD 4 then v 4 else 0) ^^^ (if x.getLsbD 5 then v 5 else 0)

private def basis : Fin 6 → Code := ![12,37,13,33,20,38]
private def coordinates (x : Code) : Code := bits ![5,39,10,11,26,13] x
private theorem reconstruct : ∀ x : Code, bits basis (coordinates x) = x := by decide

private theorem additive_ext (f : symmetryGroup) (x : Code) :
    f.val x = bits (fun i => f.val (basis i)) (coordinates x) := by
  conv_lhs => rw [← reconstruct x]
  simp only [bits, ((mem_symmetryGroup _).mp f.property).1, apply_ite f.val, symmetry_zero]

private def pair (i : Fin 3) (r : Fin 6) : Code × Code :=
  let a := (generators i.castSucc.castSucc.castSucc).1
  let b := (generators i.castSucc.castSucc.castSucc).2
  ![(a,b),(a,a ^^^ b),(b,a),(b,a ^^^ b),(a ^^^ b,a),(a ^^^ b,b)] r

private theorem pair_complete (i : Fin 3) (a b : Code)
    (ha : a ∈ line i.castSucc.castSucc.castSucc) (hb : b ∈ line i.castSucc.castSucc.castSucc)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    ∃ r : Fin 6, pair i r = (a,b) := by
  fin_cases i <;>
    simp only [line, Finset.mem_insert, Finset.mem_singleton] at ha hb <;>
    rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    first | contradiction | decide

private def images (r s t : Fin 6) : Fin 6 → Code :=
  ![(pair 0 r).1,(pair 0 r).2,(pair 1 s).1,(pair 1 s).2,(pair 2 t).1,(pair 2 t).2]

private theorem rigid : ∀ r s t : Fin 6,
    (∀ i : Fin 6, bits (images r s t) (coordinates (generators i).1) ∈ line i ∧
      bits (images r s t) (coordinates (generators i).2) ∈ line i) →
    ∀ x : Code, x ≠ 0 → bits (images r s t) (coordinates x) = x →
      images r s t = basis := by decide

private theorem kernel_mem_line (f : action.ker) (i : Fin 6) (x : Code)
    (hx : x ∈ line i) : f.val.val x ∈ line i := by
  have h := (action_mem_line f.val i x).mpr hx
  have he : action f.val = 1 := f.property
  simpa only [he, Equiv.Perm.one_apply] using h

theorem kernel_fix_nonzero (f : action.ker) (x : Code) (hx : x ≠ 0)
    (hfix : f.val.val x = x) : f = 1 := by
  have hn (x : Code) (hx : x ≠ 0) : f.val.val x ≠ 0 := by
    rw [← symmetry_zero f.val]
    exact fun h => hx (f.val.val.injective h)
  have pair_image (i : Fin 3) : ∃ r : Fin 6,
      pair i r = (f.val.val (generators i.castSucc.castSucc.castSucc).1,
        f.val.val (generators i.castSucc.castSucc.castSucc).2) := by
    apply pair_complete
    · exact kernel_mem_line f _ _ (by simp [line])
    · exact kernel_mem_line f _ _ (by simp [line])
    · exact hn _ (exceptional_nonzero _ (generators_exceptional _).1)
    · exact hn _ (exceptional_nonzero _ (generators_exceptional _).2.1)
    · exact fun h => generators_distinct _ (f.val.val.injective h)
  obtain ⟨r, hr⟩ := pair_image 0
  obtain ⟨s, hs⟩ := pair_image 1
  obtain ⟨t, ht⟩ := pair_image 2
  have him : images r s t = fun i => f.val.val (basis i) := by
    funext i
    fin_cases i <;> first
      | exact congrArg Prod.fst hr
      | exact congrArg Prod.snd hr
      | exact congrArg Prod.fst hs
      | exact congrArg Prod.snd hs
      | exact congrArg Prod.fst ht
      | exact congrArg Prod.snd ht
  have hb := rigid r s t (by
    intro i
    rw [him, ← additive_ext, ← additive_ext]
    exact ⟨kernel_mem_line f i _ (by simp [line]), kernel_mem_line f i _ (by simp [line])⟩) x hx (by rw [him, ← additive_ext]; exact hfix)
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change f.val.val x = x
  rw [additive_ext, ← him, hb, reconstruct]

theorem kernel_fix_twelve (f : action.ker) (hfix : f.val.val 12 = 12) : f = 1 :=
  kernel_fix_nonzero f 12 (by decide) hfix

theorem kernel_card_le : Nat.card action.ker ≤ 3 := by
  let target : Finset Code := {12,37,41}
  have ht : ∀ f : action.ker, f.val.val 12 ∈ target := by
    intro f
    have hm := kernel_mem_line f 0 12 (by decide)
    have hn : f.val.val 12 ≠ 0 := by
      rw [← symmetry_zero f.val]
      exact fun he => (by decide : (12 : Code) ≠ 0) (f.val.val.injective he)
    change f.val.val 12 ∈ ({0,12,37,41} : Finset Code) at hm
    simpa only [target, Finset.mem_insert, Finset.mem_singleton, hn, false_or] using hm
  let ev : action.ker → {x : Code // x ∈ target} := fun f => ⟨f.val.val 12, ht f⟩
  have hi : Function.Injective ev := by
    intro f g h
    have he : f.val.val 12 = g.val.val 12 := congrArg Subtype.val h
    have hf : (g⁻¹ * f : action.ker) = 1 := kernel_fix_twelve _ (by
      change g.val.val.symm (f.val.val 12) = 12
      rw [he, g.val.val.symm_apply_apply])
    exact (inv_mul_eq_one.mp hf).symm
  have hc := Nat.card_le_card_of_injective ev hi
  have he : Nat.card {x : Code // x ∈ target} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  exact he ▸ hc

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
