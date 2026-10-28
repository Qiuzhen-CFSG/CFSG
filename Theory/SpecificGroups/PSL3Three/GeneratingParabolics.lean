module

public import Theory.SpecificGroups.PSL3Three.FiniteModel
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum

/-!
# Two Sylow-containing parabolics generating PSL₃(3)

The stabilizers of the first coordinate line and its complementary coordinate
plane generate SL₃(3): every elementary transvection belongs to one of them,
and diagonal matrices belong to both. Their intersection contains the
centralizer of diag(1,-1,-1), which is GL₂(3) of order 48. Its Sylow subgroup
has order 16 and is therefore Sylow in SL₃(3), of order 5616.

The literal quotient map transports the generating pair and the common Sylow
subgroup to PSL₃(3). These facts, together with solvability of the parabolics,
supply the inner p=3 branch of Aschbacher--Smith E.1.14(7), printed p.214,
via E.1.12--13. The source for the concrete parabolics is GLS III, 6.5.3(a),
`refs/KGroup/GLS3/chapter6.tex`.
-/

public section
namespace Matrix.PSL3Three
open Subgroup

private def z : SL := ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by decide⟩
private theorem hz : orderOf z = 2 :=
  orderOf_eq_prime (by decide : z ^ 2 = 1) (by decide : z ≠ 1)

private theorem centralizer_le_parabolics :
    centralizer ({z} : Set SL) ≤ lineStabilizerSL ⊓ planeStabilizerSL := by
  intro g hg
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hm := congrArg (fun a : SL => a.val) hc
  change g.val * z.val = z.val * g.val at hm
  have he (i j : Fin 3) := congrArg (fun a : Matrix (Fin 3) (Fin 3) (ZMod 3) => a i j) hm
  have h10 := he 1 0
  have h20 := he 2 0
  have h01 := he 0 1
  have h02 := he 0 2
  simp [z, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h01 h02
  have hzero : ∀ a : ZMod 3, a = -a → a = 0 := by decide
  exact ⟨(mem_lineStabilizerSL_iff g).mpr ⟨hzero _ h10, hzero _ h20⟩,
    (mem_planeStabilizerSL_iff g).mpr ⟨hzero _ h01.symm, hzero _ h02.symm⟩⟩

/-- The two complementary parabolics generate SL₃(3). -/
theorem lineStabilizer_sup_planeStabilizerSL : lineStabilizerSL ⊔ planeStabilizerSL = ⊤ := by
  apply top_unique
  intro g _
  apply SpecialLinearGroup.diagonal_transvection_induction'
    (fun x => x ∈ lineStabilizerSL ⊔ planeStabilizerSL) g
  · intro i j hij a ha
    apply mem_sup_left
    rw [mem_lineStabilizerSL_iff, SpecialLinearGroup.diag2n_coe]
    simp
  · intro i j hij a
    have h : ∀ (i j : Fin 3) (hij : i ≠ j) (a : ZMod 3),
        SpecialLinearGroup.transvection hij a ∈ lineStabilizerSL ∨
        SpecialLinearGroup.transvection hij a ∈ planeStabilizerSL := by
      simp only [mem_lineStabilizerSL_iff, mem_planeStabilizerSL_iff]
      decide
    exact (h i j hij a).elim mem_sup_left mem_sup_right
  · intro a b ha hb
    exact (lineStabilizerSL ⊔ planeStabilizerSL).mul_mem ha hb

/-- The two complementary parabolics contain a common Sylow two-subgroup. -/
theorem exists_sylowTwo_le_parabolicsSL : ∃ T : Sylow 2 SL,
    (T : Subgroup SL) ≤ lineStabilizerSL ∧ (T : Subgroup SL) ≤ planeStabilizerSL := by
  let C := centralizer ({z} : Set SL)
  let P : Sylow 2 C := Classical.choice inferInstance
  have hC : Nat.card C = 48 := by
    rw [Nat.card_congr (SL3.involutionCentralizerEquiv (ZMod 3) z hz (by decide)).toEquiv,
      Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
  have hP : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity, hC]
    decide +kernel
  let S := (P : Subgroup C).map C.subtype
  have hS : Nat.card S = 16 := by
    rw [← Nat.card_congr ((P : Subgroup C).equivMapOfInjective
      C.subtype C.subtype_injective).toEquiv]
    exact hP
  let T : Sylow 2 SL := Sylow.ofCard S (by rw [hS, card_SL]; decide +kernel)
  have hTC : (T : Subgroup SL) ≤ C := map_subtype_le _
  exact ⟨T, (hTC.trans centralizer_le_parabolics).trans inf_le_left,
    (hTC.trans centralizer_le_parabolics).trans inf_le_right⟩

/-- The images of the two parabolics generate the actual projective quotient. -/
theorem lineStabilizer_sup_planeStabilizer : lineStabilizer ⊔ planeStabilizer = ⊤ := by
  rw [lineStabilizer, planeStabilizer, ← Subgroup.map_sup, lineStabilizer_sup_planeStabilizerSL,
    Subgroup.map_top_of_surjective _ project_surjective]

/-- A common Sylow two-subgroup in the actual projective quotient. -/
theorem exists_sylowTwo_le_parabolics : ∃ T : Sylow 2 PSL,
    (T : Subgroup PSL) ≤ lineStabilizer ∧ (T : Subgroup PSL) ≤ planeStabilizer := by
  obtain ⟨T, hline, hplane⟩ := exists_sylowTwo_le_parabolicsSL
  exact ⟨T.mapSurjective (f := project) project_surjective,
    map_mono hline, map_mono hplane⟩

end Matrix.PSL3Three
