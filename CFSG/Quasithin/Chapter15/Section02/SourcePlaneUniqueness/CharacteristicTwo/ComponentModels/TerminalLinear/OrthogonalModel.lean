module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Complete
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

/-!
# No orthogonal-six offender inside the marked four-block core

The actual core V₄×V₄ preserves two blocks of four. B.3.2(6) leaves an
even disjoint-pair group of order eight or a regular group of order eight.
The latter cannot preserve the blocks. In the former each point has at
most two images, whereas a permutation in V₄×V₄ is determined by its
images of 0 and 4, giving order at most four. Thus neither occurs.

Source: Aschbacher--Smith 15.2.23(c), p.1117, using B.3.2(6), pp.83--84.
-/

public section
open Subgroup Equiv Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear.OrthogonalModel
open ChapterB.Offenders ChapterB.Offenders.Eight
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
abbrev S8 := Equiv.Perm (Fin 8)

private theorem conjugate_le_alternating {A : Subgroup S8} {g : S8}
    (h : A.map (MulAut.conj g).toMonoidHom ≤ alternatingGroup (Fin 8)) :
    A ≤ alternatingGroup (Fin 8) := by
  intro a ha
  have hh := Perm.mem_alternatingGroup.mp
    (h (mem_map_of_mem (MulAut.conj g).toMonoidHom ha))
  rw [Perm.mem_alternatingGroup]
  change Perm.sign (g*a*g⁻¹) = 1 at hh
  rw [map_mul, map_mul, map_inv] at hh
  have he : Perm.sign g * Perm.sign a * (Perm.sign g)⁻¹ = Perm.sign a := by
    rw [mul_comm (Perm.sign g) (Perm.sign a), mul_assoc, mul_inv_cancel, mul_one]
  exact he.symm.trans hh

/-- Among the case-(b) offenders, only the even-pair family lies in A₈. -/
theorem even_caseB_is_evenPart {A : Subgroup S8}
    (hA : CaseBFamily 8 (by decide) A) (ha : A ≤ alternatingGroup (Fin 8)) :
    IsConjugateTo A (evenPart 8) := by
  rcases hA with h | ⟨g,rfl⟩ | h | ⟨B,hB,hne,g,rfl⟩
  · exact (h.not_le_alternating ha).elim
  · have hh := conjugate_le_alternating ha
    have hm : pairSwap 8 2 ∈ exceptional 8 (by decide) :=
      subset_closure (Or.inr ⟨2,by decide,rfl⟩)
    have he := Perm.mem_alternatingGroup.mp (hh hm)
    exact (by decide : Perm.sign (pairSwap 8 2) ≠ 1) he |>.elim
  · exact h
  · have hBE : B ≤ evenPart 8 := le_inf hB.le (conjugate_le_alternating ha)
    rcases hB.eq_or_eq hBE inf_le_left with he | he
    · exact (hne he.symm).elim
    · exact (evenPart_covBy_D.lt.ne he).elim

private theorem klein_le_alternating : kleinGroup ≤ alternatingGroup (Fin 8) := by
  rintro x ⟨a,b,rfl⟩
  rw [Perm.mem_alternatingGroup]
  exact (by decide : ∀ a b, Perm.sign (kleinPerm a b) = 1) a b

private def partner : Fin 8 → Fin 8 := ![1,0,3,2,5,4,7,6]

private theorem d_pair (g : S8) (hg : g ∈ D 8) (i : Fin 8) :
    g i = i ∨ g i = partner i := by
  obtain ⟨a,rfl⟩ := (mem_D_iff g).mp hg
  exact (by decide : ∀ a i, dWords a i = i ∨ dWords a i = partner i) a i

private theorem conjugateD_pair (r : S8) {g : S8}
    (hg : g ∈ (D 8).map (MulAut.conj r).toMonoidHom) (i : Fin 8) :
    g i ∈ ({i,r (partner (r.symm i))} : Finset (Fin 8)) := by
  obtain ⟨a,ha,rfl⟩ := hg
  rcases d_pair a ha (r.symm i) with he | he
  · apply Finset.mem_insert.mpr
    left
    change r (a (r.symm i)) = i
    rw [he,r.apply_symm_apply]
  · apply Finset.mem_insert.mpr
    right
    apply Finset.mem_singleton.mpr
    change r (a (r.symm i)) = r (partner (r.symm i))
    rw [he]

private theorem klein_determined (g h : S8) (hg : g ∈ kleinGroup)
    (hh : h ∈ kleinGroup) (h0 : g 0 = h 0) (h4 : g 4 = h 4) : g = h := by
  obtain ⟨a,b,rfl⟩ := hg
  obtain ⟨c,d,rfl⟩ := hh
  exact (by decide : ∀ a b c d, kleinPerm a b 0 = kleinPerm c d 0 →
    kleinPerm a b 4 = kleinPerm c d 4 → kleinPerm a b = kleinPerm c d) a b c d h0 h4

/-- A subgroup of the four-block core with pair orbits has order at most four. -/
theorem card_le_four_of_pair_orbits (A : Subgroup S8) (hA : A ≤ kleinGroup)
    (r : S8) (hD : A ≤ (D 8).map (MulAut.conj r).toMonoidHom) : Nat.card A ≤ 4 := by
  classical
  let F (i : Fin 8) := ({i,r (partner (r.symm i))} : Finset (Fin 8))
  let f : A → F 0 × F 4 := fun a =>
    (⟨a.val 0,conjugateD_pair r (hD a.property) 0⟩,
      ⟨a.val 4,conjugateD_pair r (hD a.property) 4⟩)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact klein_determined a.val b.val (hA a.property) (hA b.property)
      (congrArg (fun p : F 0 × F 4 => p.1.val) he)
      (congrArg (fun p : F 0 × F 4 => p.2.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  have h0 : Nat.card (F 0) ≤ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two
  have h4 : Nat.card (F 4) ≤ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two
  rw [Nat.card_prod] at hc
  exact hc.trans (by nlinarith)

/-- The genuine B.3.2(6) list has no member in the marked four-block core. -/
theorem not_isOffender_of_le_kleinGroup (A : Subgroup S8) (hA : A ≤ kleinGroup) :
    ¬ IsOffender (BinaryPermutation.naturalRepresentation (Fin 8)) A := by
  intro hoff
  rcases EightExhaustion.caseBFamily_or_isRegularEight_of_isOffender_natural hoff with hb | hr
  · obtain ⟨r,he⟩ := even_caseB_is_evenPart hb (hA.trans klein_le_alternating)
    have hD : A ≤ (D 8).map (MulAut.conj r).toMonoidHom :=
      he ▸ map_mono inf_le_left
    have hcard : Nat.card A = 8 := by
      rw [he, ← Nat.card_congr ((evenPart 8).equivMapOfInjective
        (MulAut.conj r).toMonoidHom (MulAut.conj r).injective).toEquiv, card_evenPart]
    have hle := card_le_four_of_pair_orbits A hA r hD
    omega
  · obtain ⟨a,ha,_⟩ := hr.2.2.2 0 4
    obtain ⟨i,j,he⟩ := hA a.property
    have hh : (a.val 0).val < 4 := by
      rw [he]
      exact (by decide : ∀ i j, (kleinPerm i j 0).val < 4) i j
    rw [ha] at hh
    omega

/-- The exclusion uses the actual intrinsic two-core of the parabolic. -/
theorem not_isOffender_of_le_fourBlockCore (A : Subgroup S8)
    (hA : A ≤ Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer.pCoreIn 2) :
    ¬ IsOffender (BinaryPermutation.naturalRepresentation (Fin 8)) A := by
  rw [fourStabilizer_pCoreIn] at hA
  exact not_isOffender_of_le_kleinGroup A hA

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear.OrthogonalModel
