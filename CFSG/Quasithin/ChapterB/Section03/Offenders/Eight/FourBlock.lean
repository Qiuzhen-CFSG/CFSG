module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Complete
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

/-!
# Offender exclusion in the four-block radical

The degree-eight offender classification reduces an even offender to the even
part of the four-swap group or a regular eight-group. The latter is transitive,
whereas the two block Klein groups preserve each block. The former contains a
pair of elements with exactly two common fixed letters; pairs in the block
radical have zero, four, or eight common fixed letters. Thus neither family
embeds in the radical. Only sixteen-element permutation calculations are used.

Source: Aschbacher--Smith B.3.2(6), pp.83--84, applied in 15.1.28, p.1103.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.FourBlock

private theorem klein_even : kleinGroup ≤ alternatingGroup (Fin 8) := by
  have he : ∀ a b : Fin 4, kleinPerm a b ∈ alternatingGroup (Fin 8) := by
    intro a b
    change Equiv.Perm.sign (kleinPerm a b) = 1
    revert a b
    decide
  rintro x ⟨a,b,rfl⟩
  exact he a b

private theorem caseB_even {A : Subgroup S8}
    (h : CaseBFamily 8 (by decide) A) (he : A ≤ alternatingGroup (Fin 8)) :
    IsConjugateTo A (evenPart 8) := by
  rcases h with ⟨m,hm,_,hc⟩ | hc | hc | ⟨C,hC,hn,hc⟩
  · have hm0 : (pairSwap 8 0) ∈ alternatingGroup (Fin 8) :=
      hc.le_alternating_iff.mp he (pairSwap_mem 0 hm)
    exact (by simp [pairSwap, Equiv.Perm.mem_alternatingGroup] : pairSwap 8 0 ∉ alternatingGroup (Fin 8)) hm0 |>.elim
  · have hm2 : (pairSwap 8 2) ∈ alternatingGroup (Fin 8) :=
      hc.le_alternating_iff.mp he (subset_closure (Or.inr ⟨2,by decide,rfl⟩))
    exact (by simp [pairSwap, Equiv.Perm.mem_alternatingGroup] : pairSwap 8 2 ∉ alternatingGroup (Fin 8)) hm2 |>.elim
  · exact hc
  · have hle : C ≤ evenPart 8 := le_inf hC.le (hc.le_alternating_iff.mp he)
    have heq : C = evenPart 8 := by
      apply le_antisymm hle
      exact (hC.eq_or_eq hle inf_le_left).resolve_right (ne_of_lt Eight.evenPart_covBy_D.lt) |>.le
    exact (hn heq).elim

private abbrev pairFixed (x y : S8) := {i : Fin 8 // x i = i ∧ y i = i}

private theorem pairFixed_conj (x y g : S8) :
    Nat.card (pairFixed (g*x*g⁻¹) (g*y*g⁻¹)) = Nat.card (pairFixed x y) := by
  let e : pairFixed x y ≃ pairFixed (g*x*g⁻¹) (g*y*g⁻¹) :=
    { toFun i := ⟨g i.val, by
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
          And.intro (congrArg g i.property.1) (congrArg g i.property.2)⟩
      invFun i := ⟨g⁻¹ i.val, by
        have h1 := congrArg (fun j : Fin 8 => g⁻¹ j) i.property.1
        have h2 := congrArg (fun j : Fin 8 => g⁻¹ j) i.property.2
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using And.intro h1 h2⟩
      left_inv _ := by ext; simp
      right_inv _ := by ext; simp }
  exact (Nat.card_congr e).symm

private theorem klein_pairFixed_ne_two (x y : S8) (hx : x ∈ kleinGroup)
    (hy : y ∈ kleinGroup) : Nat.card (pairFixed x y) ≠ 2 := by
  obtain ⟨a,b,rfl⟩ := hx
  obtain ⟨c,d,rfl⟩ := hy
  rw [Nat.card_eq_fintype_card]
  have h : ∀ a b c d : Fin 4,
      Fintype.card (pairFixed (kleinPerm a b) (kleinPerm c d)) ≠ 2 := by decide
  exact h a b c d

private theorem no_evenPart (g : S8) :
    ¬ (evenPart 8).map (MulAut.conj g).toMonoidHom ≤ kleinGroup := by
  intro h
  let x : S8 := pairSwap 8 0 * pairSwap 8 1
  let y : S8 := pairSwap 8 0 * pairSwap 8 2
  have hx : x ∈ evenPart 8 := ⟨(D 8).mul_mem (pairSwap_mem 0 (by decide))
    (pairSwap_mem 1 (by decide)), by
      change Equiv.Perm.sign _ = 1
      decide⟩
  have hy : y ∈ evenPart 8 := ⟨(D 8).mul_mem (pairSwap_mem 0 (by decide))
    (pairSwap_mem 2 (by decide)), by
      change Equiv.Perm.sign _ = 1
      decide⟩
  have hf := klein_pairFixed_ne_two _ _ (h (mem_map_of_mem _ hx)) (h (mem_map_of_mem _ hy))
  change Nat.card (pairFixed (g*x*g⁻¹) (g*y*g⁻¹)) ≠ 2 at hf
  rw [pairFixed_conj] at hf
  apply hf
  rw [Nat.card_eq_fintype_card]
  decide

/-- The four-block radical contains no offender on the six-dimensional natural module. -/
theorem no_offender {A : Subgroup S8} (hAK : A ≤ kleinGroup) :
    ¬ IsOffender (naturalRepresentation (Fin 8)) A := by
  intro hA
  rcases EightExhaustion.caseBFamily_or_isRegularEight_of_isOffender_natural hA with hc | hr
  · obtain ⟨g,hg⟩ := caseB_even hc (hAK.trans klein_even)
    exact no_evenPart g (hg ▸ hAK)
  · obtain ⟨a,ha,_⟩ := hr.2.2.2 0 4
    obtain ⟨b,c,hbc⟩ := hAK a.property
    have h : ∀ b c : Fin 4, kleinPerm b c 0 ≠ (4 : Fin 8) := by decide
    exact h b c (hbc ▸ ha)

end CFSG.Quasithin.ChapterB.Offenders.Eight.FourBlock
