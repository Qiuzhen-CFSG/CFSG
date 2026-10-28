module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.SpecificGroups.PSL3Even.InvolutionResidualRows.Cases
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualLinear
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveField
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField

/-!
# Linear three-dimensional components in characteristic two

This file records the actual matrix actions used for the linear-three row of
Aschbacher--Smith 16.1.4 and 16.1.6.  The model is always the concrete
quotient `SL₃(F) / Z(SL₃(F))`; an abstract component is transported through the
specified multiplicative equivalence.  In particular, the alternatives below
retain the matrix `GL₃` actor, the coefficient-field automorphism, and the
inverse-transpose graph actor (with coordinate reversal in the first normal form).  No group-family label is used as a substitute
for an induced action.

The general field and graph residuals, the larger graph-field residuals,
and the inner root/parabolic row are proved in `InvolutionResidualRows`.
The Sylow-fixer calculation proves the linear-three case of 16.1.6, even
without the two-power-order restriction. The exhaustive residual assembly
retains exactly one premise: a compatible marking of every twisted
GF(4) graph-field involution by the standard action. The three standard
GF(4) residual calculations below have no extra premise beyond the specified
intertwining equivalence. Final source-table assembly must discharge the
remaining marking premise.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3.LinearThree
open Matrix.PSL3Even.UnipotentGeometry

namespace CFSG.Quasithin.Chapter16.LiePreliminaries

/-! ### Actual automorphism actions -/

/-- The concrete standard normal form for a binary `PSL₃` model.  The two
branches are the field coset and the graph coset, with the full linear matrix
factor retained. -/
theorem linearThree_standard_normal_form {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hn : 0 < n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (a : MulAut L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_hF : Nat.card F = 2 ^ n)
      (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (m : GL (Fin 3) F) (σ : F ≃+* F),
      (MulAut.congr e a =
          linearConj F m * fieldAction F σ ∨
        MulAut.congr e a =
          linearConj F m * fieldAction F σ *
            Matrix.PSL3.OuterSolvable.OddPrimeCoverage.oppositionGraph F) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let _ : Field F := hF
  let _ : Finite F := hfin
  have hcover : standard F = ⊤ :=
    standard_eq_top_of_two_power_card F hn hcard
  obtain ⟨m, σ, h | h⟩ :=
    Matrix.PSL3.CartanActions.ResidualLinear.standard_opposition_factorization
      (F := F) (MulAut.congr e a) (by rw [hcover]; trivial)
  · exact ⟨F, inferInstance, inferInstance, hcard, e, m, σ, Or.inl h⟩
  · exact ⟨F, inferInstance, inferInstance, hcard, e, m, σ, Or.inr h⟩

/-- An involution in a linear coset is inner.  This is the projective version
of the determinant-correction argument: the matrix action is the actual
`GL₃` conjugation action on the quotient, so no abstract diagonal label is
introduced. -/
theorem linearThree_linear_involution_inner {L : Type*} [Group L] [Finite L]
    (F : Type) [Field F] [Finite F] (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (m : GL (Fin 3) F) (a : MulAut L)
    (ha : (MulAut.congr e a) = linearConj F m)
    (ha2 : a ^ 2 = 1) :
    ∃ x : L, a = MulAut.conj x := by
  have hb2 : (linearConj F m) ^ 2 = 1 := by
    rw [← ha, ← map_pow, ha2, map_one]
  obtain ⟨x, hx⟩ := Matrix.PSL3.OddInvolutionFixed.linearConj_involution_inner m hb2
  apply (MulAut.congr_inner_iff e a).mp
  refine ⟨x, ?_⟩
  rw [ha]
  exact hx.symm

/-- The coarse involutory alternatives retain the actual coefficient and
opposition graph actions, including their linear twists. The source residual
refinements are assembled in `linearThree_involution_models_of_four_marking`. -/
theorem linearThree_involution_alternative {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hn : 0 < n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (a : MulAut L) (ha : orderOf a = 2) :
    (∃ x : L, a = MulAut.conj x) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_hF : Nat.card F = 2 ^ n)
      (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (m : GL (Fin 3) F) (σ : F ≃+* F),
      σ ≠ 1 ∧ MulAut.congr e a = linearConj F m * fieldAction F σ) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_hF : Nat.card F = 2 ^ n)
      (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (m : GL (Fin 3) F) (σ : F ≃+* F),
      σ = 1 ∧ MulAut.congr e a = linearConj F m *
        Matrix.PSL3.OuterSolvable.OddPrimeCoverage.oppositionGraph F) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (_hF : Nat.card F = 2 ^ n)
      (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (m : GL (Fin 3) F) (σ : F ≃+* F),
      σ ≠ 1 ∧ MulAut.congr e a = linearConj F m * fieldAction F σ *
        Matrix.PSL3.OuterSolvable.OddPrimeCoverage.oppositionGraph F) := by
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨F, hF, hfin, hcard, e, m, σ, h | h⟩ :=
    linearThree_standard_normal_form hn hmodel a
  · by_cases hσ : σ = 1
    · left
      exact linearThree_linear_involution_inner F e m a
        (by simpa only [hσ, map_one, mul_one] using h) ha2
    · exact Or.inr (Or.inl ⟨F, hF, hfin, hcard, e, m, σ, hσ, h⟩)
  · by_cases hσ : σ = 1
    · exact Or.inr (Or.inr (Or.inl ⟨F, hF, hfin, hcard, e, m, σ, hσ,
        by simpa only [hσ, map_one, mul_one] using h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨F, hF, hfin, hcard, e, m, σ, hσ, h⟩))

/-! ### Pointwise Sylow fixation and the long-root refinement -/

/-- The pointwise Sylow fixer in 16.1.6, transported through an actual
`PSL₃(F)` model.  The conjugating element lies in the image of the centre of
the specified Sylow subgroup. -/
theorem linearThree_sylow_fixing_inner {J : Type*} [Group J] [Finite J]
    {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (S : Sylow 2 J) (a : MulAut J) (hfix : ∀ s ∈ S, a s = s) :
    ∃ z ∈ (center S).map (S : Subgroup J).subtype, a = MulAut.conj z :=
  Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv F hn hF e S a hfix

/-- The nontrivial involutory pointwise fixer is a genuine long-root action.
The element is displayed in the highest-root matrix coordinates of a
conjugated model, so the endpoint `n = 1` is retained. -/
theorem linearThree_sylow_fixing_long_root {J : Type*} [Group J] [Finite J]
    {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (S : Sylow 2 J) (a : MulAut J) (hfix : ∀ s ∈ S, a s = s)
    (ha1 : a ≠ 1) :
    ∃ (f : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃* J) (c : F),
      c ≠ 0 ∧ a = MulAut.conj (f (projective F ⟨0, 0, c⟩)) := by
  let P := (Matrix.PSL3.LinearThree.unipotentSylow F hn hF).mapSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P S
  let f : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃* J :=
    e.symm.trans (MulAut.conj g)
  have hS : (unipotent F).map f.toMonoidHom = (S : Subgroup J) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent F).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = _ at hh
    change (unipotent F).map
      ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hh
  let b : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (f.trans a).trans f.symm
  have hbfix : ∀ u ∈ unipotent F, b u = u := by
    intro u hu
    change f.symm (a (f u)) = u
    have hfu : f u ∈ (S : Subgroup J) := by
      rw [← hS]
      exact mem_map_of_mem f.toMonoidHom hu
    rw [hfix (f u) hfu]
    exact f.symm_apply_apply u
  obtain ⟨z, hz, hb⟩ :=
    Matrix.PSL3.LinearThree.exists_projectiveCenter_of_fixes_unipotent
      F hn hF b hbfix
  obtain ⟨c, hc⟩ := (mem_projectiveCenter F z).mp hz
  have hc0 : c ≠ 0 := by
    intro hc0
    apply ha1
    have hz0 : z = 1 := by
      rw [← hc]
      rw [hc0]
      change (projective F) (1 : Matrix.PSL3Even.UnipotentGeometry.U F) = 1
      exact (projective F).map_one
    ext x
    have hh := congrArg f (DFunLike.congr_fun hb (f.symm x))
    change f (f.symm (a (f (f.symm x)))) = f (z * f.symm x * z⁻¹) at hh
    simpa only [f.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply, hz0,
      inv_one, mul_one, one_mul, MulAut.one_apply] using hh
  refine ⟨f, c, hc0, ?_⟩
  ext x
  have hh := congrArg f (DFunLike.congr_fun hb (f.symm x))
  change f (f.symm (a (f (f.symm x)))) = f (z * f.symm x * z⁻¹) at hh
  simpa only [f.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply, hc] using hh

/-! ### Residual transport -/

/-- Transport a fixed two-residual through the actual model equivalence. -/
noncomputable def linearThree_fixedResidualTransport {J : Type*} [Group J]
    {F : Type*} [Field F] [Finite F]
    (e : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (a : MulAut J) (b : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (heq : ∀ x, e (a x) = b (e x)) :
    pResidual 2 a.fixedSubgroup ≃*
      pResidual 2 b.fixedSubgroup :=
  MulAut.fixedResidualEquivOfCompatible 2 e a b heq

theorem linearThree_fixedResidualTransport_apply {J : Type*} [Group J]
    {F : Type*} [Field F] [Finite F]
    (e : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (a : MulAut J) (b : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (heq : ∀ x, e (a x) = b (e x))
    (x : pResidual 2 a.fixedSubgroup) :
    ((linearThree_fixedResidualTransport e a b heq x :
      pResidual 2 b.fixedSubgroup) : b.fixedSubgroup) = e (x : a.fixedSubgroup) :=
  MulAut.fixedResidualEquivOfCompatible_apply 2 e a b heq x

/-! ### The concrete `PSL₃(4)` endpoint -/

/-- The field row at `PSL₃(4)`: the fixed two-residual is the actual
`PSL₃(2)` matrix group, transported through the supplied model action. -/
noncomputable def linearThree_four_field_fixedResidual
    {J : Type*} [Group J] (e : J ≃* Matrix.PSL3Four.PSL) (a : MulAut J)
    (heq : ∀ x, e (a x) = Matrix.PSL3Four.pslFrobenius (e x)) :
    pResidual 2 a.fixedSubgroup ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (linearThree_fixedResidualTransport e a Matrix.PSL3Four.pslFrobenius heq).trans
    Matrix.PSL3Four.projectiveFieldResidualEquiv

/-- The graph row at `PSL₃(4)`: the fixed two-residual is the actual
`PSL₂(4)` matrix group. -/
noncomputable def linearThree_four_graph_fixedResidual
    {J : Type*} [Group J] (e : J ≃* Matrix.PSL3Four.PSL) (a : MulAut J)
    (heq : ∀ x, e (a x) = Matrix.PSL3.OuterSolvable.graph Matrix.PSL3Four.F (e x)) :
    pResidual 2 a.fixedSubgroup ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) Matrix.PSL3Four.F :=
  (linearThree_fixedResidualTransport e a
      (Matrix.PSL3.OuterSolvable.graph Matrix.PSL3Four.F) heq).trans
    Matrix.PSL3Four.projectiveGraphResidualEquiv

/-- The graph-field row at `PSL₃(4)`: the exceptional endpoint residual is
the genuine elementary group `E₉ = (Z/3)^2`. -/
noncomputable def linearThree_four_graphField_fixedResidual
    {J : Type*} [Group J] (e : J ≃* Matrix.PSL3Four.PSL) (a : MulAut J)
    (heq : ∀ x, e (a x) =
      (Matrix.PSL3.OuterSolvable.graph Matrix.PSL3Four.F *
        Matrix.PSL3Four.pslFrobenius) (e x)) :
    pResidual 2 a.fixedSubgroup ≃*
      Multiplicative (Fin 2 → ZMod 3) :=
  (linearThree_fixedResidualTransport e a
      (Matrix.PSL3.OuterSolvable.graph Matrix.PSL3Four.F *
        Matrix.PSL3Four.pslFrobenius) heq).trans
    Matrix.PSL3Four.projectiveGraphFieldResidualEquiv

/-- All source rows for an actual linear-three model, conditional only on the
remaining degree-two graph-field marking. This premise must be discharged
before using the result as the unconditional source theorem. -/
theorem linearThree_involution_models_of_four_marking {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hn : 0 < n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (hsmall : ∀ (F : Type) [Field F] [Finite F],
      Matrix.PSL3Even.InvolutionResidualRows.FourGraphFieldMarking F)
    (a : MulAut L) (ha : orderOf a = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_hF : Nat.card F = 2 ^ n)
      (e : L ≃* PSL(3,F)),
      Matrix.PSL3Even.InvolutionResidualRows.RootParabolicCase (MulAut.congr e a) ∨
      Matrix.PSL3Even.InvolutionResidualRows.FieldCase n (MulAut.congr e a) ∨
      Matrix.PSL3Even.InvolutionResidualRows.GraphCase (MulAut.congr e a) ∨
      Matrix.PSL3Even.InvolutionResidualRows.GraphFieldCase n (MulAut.congr e a) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  exact ⟨F, hF, hfin, hcard, e,
    Matrix.PSL3Even.InvolutionResidualRows.involution_cases_of_four_marking hn hcard
      (hsmall F) (MulAut.congr e a) (by rw [(MulAut.congr e).orderOf_eq, ha])⟩

end CFSG.Quasithin.Chapter16.LiePreliminaries
