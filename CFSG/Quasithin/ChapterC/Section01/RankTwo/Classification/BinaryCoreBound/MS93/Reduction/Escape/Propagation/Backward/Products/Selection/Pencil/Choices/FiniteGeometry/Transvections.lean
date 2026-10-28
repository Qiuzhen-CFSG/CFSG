module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes
/-!
# Two planes moved by a binary transvection

The three coordinate planes are `v₀ = 0`, `v₁ = 0`, and `v₀ + v₁ = 0`.
They meet `v₂ = 0` in its three different lines. Every nonidentity element
of its pointwise fixer is a shear with nonzero direction `(a,b,0)`. Exactly
two of the displayed planes miss that direction, so the shear moves them:
the vector e₂ lies in both planes and its image `(a,b,1)` lies outside them.
Their maximal stabilizers therefore generate SL₃(2) with any subgroup
containing that shear.

The witnesses are explicit determinant-one matrices and coordinate vectors.
Source: Meierfrankenfeld--Stellmacher (1993), the distinct-line choices in
the proof of (4.3.7)(i), printed p.887.
-/

@[expose] public section

open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry

def crossActor : Fin 3 → SL := ![
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩,
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩,
  ⟨!![1, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩]

def crossEval (i : Fin 3) (v : Fin 3 → ZMod 2) : ZMod 2 := ![v 0, v 1, v 0 + v 1] i

theorem mem_crossPlane (i : Fin 3) (v : Space) :
    v ∈ move (crossActor i) standardPlane ↔ crossEval i v.toAdd = 0 := by
  change v ∈ standardPlane.map (modelAction (crossActor i)).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  change (((crossActor i)⁻¹).val.mulVec v.toAdd) 2 = 0 ↔ _
  have test : ∀ (i : Fin 3) (v : Fin 3 → ZMod 2),
      (((crossActor i)⁻¹).val.mulVec v) 2 = crossEval i v := by decide +kernel
  rw [test]

-- Each nontrivial shear misses two of the three different lines in v₂ = 0.
theorem shear_choices : ∀ c : Multiplicative (ZMod 2 × ZMod 2),
    BinaryLinearThree.shear c ≠ 1 → ∃ i j : Fin 3,
      crossEval i ![c.toAdd.1, c.toAdd.2, 1] ≠ 0 ∧
      crossEval j ![c.toAdd.1, c.toAdd.2, 1] ≠ 0 ∧
      ∃ v : Fin 3 → ZMod 2,
        v 2 = 0 ∧ crossEval i v = 0 ∧ crossEval j v ≠ 0 := by
  intro c hc
  have small : ∀ a b : ZMod 2, (a ≠ 0 ∨ b ≠ 0) → ∃ i j : Fin 3,
      crossEval i ![a, b, 1] ≠ 0 ∧ crossEval j ![a, b, 1] ≠ 0 ∧
      ∃ v : Fin 3 → ZMod 2,
        v 2 = 0 ∧ crossEval i v = 0 ∧ crossEval j v ≠ 0 := by
    intro a b hn
    fin_cases a <;> fin_cases b
    · rcases hn with hn | hn <;> exact (hn rfl).elim
    · exact ⟨1, 2, by decide, by decide, ![1, 0, 0], by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, ![0, 1, 0], by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, ![0, 1, 0], by decide, by decide, by decide⟩
  apply small
  by_contra hn
  push Not at hn
  have he : c = 1 := Prod.ext hn.1 hn.2
  exact hc (by rw [he, map_one])

theorem shear_not_stabilizing (c : Multiplicative (ZMod 2 × ZMod 2)) (i : Fin 3)
    (hc : crossEval i ![c.toAdd.1, c.toAdd.2, 1] ≠ 0) :
    BinaryLinearThree.shear c ∉ planeStabilizer (move (crossActor i) standardPlane) := by
  intro h
  have hz : Multiplicative.ofAdd (![0, 0, 1] : Fin 3 → ZMod 2) ∈
      move (crossActor i) standardPlane := by
    rw [mem_crossPlane]
    have test : ∀ i : Fin 3, crossEval i ![0, 0, 1] = 0 := by decide
    exact test i
  have ht := (mem_planeStabilizer_iff _ _).mp h _ hz
  rw [mem_crossPlane] at ht
  have he : modelAction (BinaryLinearThree.shear c)
      (Multiplicative.ofAdd ![0, 0, 1]) = Multiplicative.ofAdd ![c.toAdd.1, c.toAdd.2, 1] := by
    change !![1, 0, c.toAdd.1; 0, 1, c.toAdd.2; 0, 0, 1].mulVec ![0, 0, 1] = ![c.toAdd.1, c.toAdd.2, 1]
    ext k
    fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  rw [he] at ht
  exact hc ht

theorem generate_of_moving (B : Subgroup Space) (hB : Nat.card B = 4)
    (K : Subgroup SL) (t : SL) (ht : t ∈ K) (hm : t ∉ planeStabilizer B) :
    planeStabilizer B ⊔ K = ⊤ := by
  apply (planeStabilizer_isCoatom B hB).2
  refine ⟨le_sup_left, ?_⟩
  intro he
  exact hm (he ((show K ≤ planeStabilizer B ⊔ K from le_sup_right) ht))

theorem standard_choices (K : Subgroup SL) (hK : Nat.card K = 2)
    (hfix : fixedSpace K = standardPlane) :
    ∃ i j : Fin 3,
      planeStabilizer (move (crossActor i) standardPlane) ⊔ K = ⊤ ∧
      planeStabilizer (move (crossActor j) standardPlane) ⊔ K = ⊤ ∧
      move (crossActor i) standardPlane ⊓ standardPlane ≠
        move (crossActor j) standardPlane ⊓ standardPlane := by
  have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, ht⟩ := exists_ne (1 : K)
  have htfix : t.val ∈ planeFixer standardPlane := by
    intro v hv
    have hvK : v ∈ fixedSpace K := hfix.symm ▸ hv
    exact hvK t.val t.property
  rw [standardPlane_fixer] at htfix
  obtain ⟨c, hc⟩ := htfix
  have hcne : BinaryLinearThree.shear c ≠ 1 := fun he => ht (Subtype.ext (hc.symm.trans he))
  have hcK : BinaryLinearThree.shear c ∈ K := hc.symm ▸ t.property
  obtain ⟨i, j, hi, hj, v, hv2, hvi, hvj⟩ := shear_choices c hcne
  refine ⟨i, j,
    generate_of_moving _ (by rw [move_card, standardPlane_card]) K _ hcK
      (shear_not_stabilizing c i hi),
    generate_of_moving _ (by rw [move_card, standardPlane_card]) K _ hcK
      (shear_not_stabilizing c j hj), ?_⟩
  intro he
  have hv : Multiplicative.ofAdd v ∈ move (crossActor i) standardPlane ⊓ standardPlane :=
    ⟨(mem_crossPlane i _).mpr hvi, hv2⟩
  rw [he] at hv
  exact hvj ((mem_crossPlane j _).mp hv.1)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
