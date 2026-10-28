module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.SpecificGroups.BinaryLinear.FiveJ2ResidualObstruction
public import Theory.SpecificGroups.SymmetricEight.InvolutionActions
public import Theory.SpecificGroups.BinaryLinear.RootCentralizerParabolic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Automorphism actions and root parabolics of PSL₄(2) and PSL₅(2)

An actual field equivalence, the center quotient, and the natural matrix
representation identify each binary PSL model with its linear action.
Pointwise Sylow fixation then forces innerness; every nonidentity such
automorphism is induced by a transvection, hence a long-root involution.
The innerness conclusion also lifts through any perfect central cover.

This supplies the higher-linear cases of Aschbacher–Smith,
*The Classification of Quasithin Groups*, 16.1.6, printed p.1172.
The eight-point action exhausts the PSL₄(2) involutory automorphisms by
cycle type and identifies the generated S₈ overgroup with its actual action.
A root centralizer lies in a proper geometric parabolic; its two-residual
agrees with the parabolic fixed two-residual as an ambient subgroup.
The A₄/A₆ residuals, their matrix type labels, and the remaining PSL₅(2)
coverage and corrected rank-two geometry remain separate obligations.
The obstruction theorem records a concrete obstruction to the literal PSL₅(2) extension printed in
16.1.4(3), which differs from the expression used in 16.5.12 on p.1200.
-/

public section

namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic

/-- Compare an arbitrary binary PSL field witness with the actual natural
binary linear action, using the matrix and quotient maps. -/
noncomputable def higherLinearEquiv {L : Type*} [Group L] {n : ℕ}
    (hn : 0 < n) (hmodel : ClassicalGroup.IsPSL L n 2) : L ≃* LinearGroup n := Classical.choice <| by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  exact ⟨e.trans ((Atlas.fieldEquivPSL n eF).trans (projectiveEquivLinear hn))⟩

private theorem fixing_inner_transport {L : Type*} [Group L] [Finite L] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (e : L ≃* LinearGroup n)
    (P : Sylow 2 L) (r : MulAut L) (hr : ∀ x ∈ P, r x = x) :
    ∃ g ∈ P, r = MulAut.conj g := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : ∀ x ∈ Q, MulAut.congr e r x = x := by
    rintro x ⟨y, hy, rfl⟩
    change e (r (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hr y hy]
  obtain ⟨g, hg, he⟩ := sylow_fixing_inner hn Q (MulAut.congr e r) hQ
  obtain ⟨x, hx, rfl⟩ := hg
  refine ⟨x, hx, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj]
  exact he

/-- The PSL₄(2) and PSL₅(2) innerness cases of 16.1.6. This stronger result
includes every automorphism of arbitrary two-power order. -/
theorem higherLinear_sylow_fixing_inner {L : Type*} [Group L] [Finite L] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hmodel : ClassicalGroup.IsPSL L n 2)
    (P : Sylow 2 L) (r : MulAut L) (hr : ∀ x ∈ P, r x = x) :
    ∃ g ∈ P, r = MulAut.conj g :=
  fixing_inner_transport hn (higherLinearEquiv (by omega) hmodel) P r hr

/-- The long-root refinement retains the natural binary action of the
conjugating element. It applies in particular when r is an involution. -/
theorem higherLinear_sylow_fixing_longRoot {L : Type*} [Group L] [Finite L] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (e : L ≃* LinearGroup n)
    (P : Sylow 2 L) (r : MulAut L) (hr : ∀ x ∈ P, r x = x) (hr1 : r ≠ 1) :
    ∃ g ∈ P, r = MulAut.conj g ∧ IsTransvection (e g) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : ∀ x ∈ Q, MulAut.congr e r x = x := by
    rintro x ⟨y, hy, rfl⟩
    change e (r (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hr y hy]
  have hne : MulAut.congr e r ≠ 1 := by
    intro he
    apply hr1
    exact (MulAut.congr e).injective (he.trans (map_one _).symm)
  obtain ⟨g, hg, he, ht⟩ := sylow_fixing_ne_one_transvection hn Q
    (MulAut.congr e r) hQ hne
  obtain ⟨x, hx, rfl⟩ := hg
  refine ⟨x, hx, (MulAut.congr e).injective ?_, ht⟩
  rw [MulAut.congr_conj]
  exact he

/-- Innerness lifts through a perfect central cover, before the parent's
multiplier argument excludes such covers in the higher-linear cases. -/
theorem higherLinear_cover_sylow_fixing_inner {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) n 2)
    (P : Sylow 2 L) (r : MulAut L) (hr : ∀ x ∈ P, r x = x) :
    ∃ g ∈ P, r = MulAut.conj g :=
  MulAut.fixing_sylow_inner_of_centralQuotient (higherLinearEquiv (by omega) hmodel)
    (fun Q a ha => sylow_fixing_inner hn Q a ha) P r hr

/-- The literal Z₃/(E₄ × E₄) row in 16.1.4(3) is false for the actual
j₂ actor on PSL₅(2). The residual here is precisely the ambient L_r used
in this chapter. This obstruction does not assert the corrected structure. -/
theorem higherLinear_psl5_printed_extension_obstruction :
    let t := BinaryLinear.FiveJ2ResidualObstruction.pslJ2
    orderOf (MulAut.conj t) = 2 ∧
      ¬ Nonempty (GroupExtension
        ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
        (fixedTwoResidual (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))
          (MulAut.conj t)) (Multiplicative (ZMod 3))) := by
  dsimp only
  refine ⟨BinaryLinear.FiveJ2ResidualObstruction.pslJ2_action_order, ?_⟩
  apply BinaryLinear.FiveJ2ResidualObstruction.model_no_elementary_cubic_extension
    (by decide)
  exact (pResidual 2 _).equivMapOfInjective
    (MulAut.conj BinaryLinear.FiveJ2ResidualObstruction.pslJ2).fixedSubgroup.subtype
    Subtype.val_injective

open Theory.SpecificGroups.SymmetricEight.Involutions

/-- The actual PSL₄(2)–A₈ comparison, including the field and projective model maps. -/
noncomputable def higherLinearFourAlternatingEquiv {L : Type*} [Group L]
    (hmodel : ClassicalGroup.IsPSL L 4 2) : L ≃* alternatingGroup (Fin 8) :=
  (higherLinearEquiv (by decide) hmodel).trans
    ((projectiveEquivLinear (by decide : 0 < 4)).symm.trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)

/-- Automorphisms of an actual PSL₄(2) model act faithfully on eight points. -/
noncomputable def higherLinearFourAutEquiv {L : Type*} [Group L]
    (hmodel : ClassicalGroup.IsPSL L 4 2) : MulAut L ≃* Equiv.Perm (Fin 8) :=
  automorphismPermutationEquiv (higherLinearFourAlternatingEquiv hmodel)

/-- Compatibility with the specified component model and its automorphism action. -/
theorem higherLinearFourAutEquiv_action {L : Type*} [Group L]
    (hmodel : ClassicalGroup.IsPSL L 4 2) (r : MulAut L) (x : L) :
    (higherLinearFourAlternatingEquiv hmodel (r x)).val =
      higherLinearFourAutEquiv hmodel r * (higherLinearFourAlternatingEquiv hmodel x).val *
        (higherLinearFourAutEquiv hmodel r)⁻¹ :=
  automorphismPermutationEquiv_action (higherLinearFourAlternatingEquiv hmodel) r x

/-- Exhaustive eight-point cycle types for the PSL₄(2) involutory automorphisms.
The root, j₂ and graph labels and their residuals are separate assertions. -/
theorem higherLinearFour_involution_cycleType {L : Type*} [Group L]
    (hmodel : ClassicalGroup.IsPSL L 4 2) (r : MulAut L) (hr : orderOf r = 2) :
    (higherLinearFourAutEquiv hmodel r).cycleType = {2} ∨
      (higherLinearFourAutEquiv hmodel r).cycleType = {2, 2} ∨
      (higherLinearFourAutEquiv hmodel r).cycleType = {2, 2, 2} ∨
      (higherLinearFourAutEquiv hmodel r).cycleType = {2, 2, 2, 2} := by
  apply involution_cycleType
  rwa [(higherLinearFourAutEquiv hmodel).orderOf_eq]

/-- The overgroup/action clauses of 16.1.4(9): the subgroup generated by
Inn(L) and the three-transposition actor is actually S₈, with the same actor,
inner embedding and action on L. This does not yet assert its A₄ residual. -/
theorem higherLinearFour_exceptional_overgroup {L : Type*} [Group L]
    (hmodel : ClassicalGroup.IsPSL L 4 2) (r : MulAut L)
    (hr : (higherLinearFourAutEquiv hmodel r).cycleType = {2, 2, 2}) :
    ∃ E : (MulAut.innerSubgroup L ⊔ zpowers r : Subgroup (MulAut L)) ≃* Equiv.Perm (Fin 8),
      (E ⟨r, (le_sup_right : zpowers r ≤ MulAut.innerSubgroup L ⊔ zpowers r)
        (mem_zpowers r)⟩).cycleType = {2, 2, 2} ∧
      Fintype.card (Function.fixedPoints (E ⟨r,
        (le_sup_right : zpowers r ≤ MulAut.innerSubgroup L ⊔ zpowers r) (mem_zpowers r)⟩)) = 2 ∧
      (∀ x : L, E ⟨MulAut.conj x, (le_sup_left : MulAut.innerSubgroup L ≤
        MulAut.innerSubgroup L ⊔ zpowers r) ⟨x, rfl⟩⟩ =
        (higherLinearFourAlternatingEquiv hmodel x).val) ∧
      ∀ (b : (MulAut.innerSubgroup L ⊔ zpowers r : Subgroup (MulAut L))) (x : L),
        (higherLinearFourAlternatingEquiv hmodel (b.val x)).val =
          E b * (higherLinearFourAlternatingEquiv hmodel x).val * (E b)⁻¹ := by
  let e := higherLinearFourAlternatingEquiv hmodel
  have hout : r ∉ MulAut.innerSubgroup L := outer_of_threePairs e r hr
  refine ⟨generatedEquivSymmetric e r hout, hr, threePairs_fixedPoints hr, ?_, ?_⟩
  · exact generatedEquivSymmetric_inner e r hout
  · intro b x
    exact automorphismPermutationEquiv_action e b.val x

/-- The higher-linear root branch of 16.1.4(1). The parabolic is the actual
stabilizer of a nonzero proper natural subspace; the residual equality retains
the inclusions in L. The transvection premise is the branch condition, not
an assumption of the parabolic or residual conclusion. -/
theorem higherLinear_root_parabolic {L : Type*} [Group L] {n : ℕ}
    (e : L ≃* LinearGroup n) (t : L) (ht : IsTransvection (e t)) :
    ∃ W : Submodule (ZMod 2) (Space n), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      let P := (BinaryLinear.parabolic W).comap e.toMonoidHom
      P ≠ ⊤ ∧ (MulAut.conj t).fixedSubgroup ≤ P ∧
        fixedTwoResidual L (MulAut.conj t) =
          (pResidual 2 (P ⊓ (MulAut.conj t).fixedSubgroup : Subgroup L)).map
            (P ⊓ (MulAut.conj t).fixedSubgroup).subtype := by
  obtain ⟨W, hW0, hW1, hP, hC⟩ :=
    BinaryLinear.RootCentralizer.transvection_proper_parabolic ht
  have hle : (MulAut.conj t).fixedSubgroup ≤
      (BinaryLinear.parabolic W).comap e.toMonoidHom := by
    intro x hx
    apply hC
    rw [MulAut.mem_fixedSubgroup] at hx ⊢
    have hh := congrArg e hx
    change e t * e x * (e t)⁻¹ = e x
    simpa only [MulAut.conj_apply, map_mul, map_inv] using hh
  refine ⟨W, hW0, hW1, ?_, hle, ?_⟩
  · intro hp
    apply hP
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ∈ (BinaryLinear.parabolic W).comap e.toMonoidHom := by rw [hp]; trivial
    exact hx
  · rw [inf_eq_right.mpr hle]
    rfl


variable {L H : Type*} [Group L] [Group H]

/-- Transport an actual marked fixed residual through a compatible model
equivalence. In particular this applies to conjugates of the corrected PSL₅(2)
j₂ row; it assumes no extension, splitting or residual structure. -/
noncomputable def higherLinearFixedResidualEquiv (e : L ≃* H)
    (a : MulAut L) (b : MulAut H) (heq : ∀ x, e (a x) = b (e x)) :
    fixedTwoResidual L a ≃* fixedTwoResidual H b :=
  ((pResidual 2 a.fixedSubgroup).equivMapOfInjective a.fixedSubgroup.subtype
    a.fixedSubgroup.subtype_injective).symm.trans
      ((MulAut.fixedResidualEquivOfCompatible 2 e a b heq).trans
        ((pResidual 2 b.fixedSubgroup).equivMapOfInjective b.fixedSubgroup.subtype
          b.fixedSubgroup.subtype_injective))

/-- Residual transport preserves each element of the ambient component. -/
theorem higherLinearFixedResidualEquiv_apply (e : L ≃* H)
    (a : MulAut L) (b : MulAut H) (heq : ∀ x, e (a x) = b (e x))
    (x : fixedTwoResidual L a) :
    (higherLinearFixedResidualEquiv e a b heq x : H) = e (x : L) := by
  let d := (pResidual 2 a.fixedSubgroup).equivMapOfInjective a.fixedSubgroup.subtype
    a.fixedSubgroup.subtype_injective
  have hx : (((d.symm x : pResidual 2 a.fixedSubgroup) : a.fixedSubgroup) : L) = x.val := by
    exact congrArg Subtype.val (d.apply_symm_apply x)
  unfold higherLinearFixedResidualEquiv
  change (b.fixedSubgroup.subtype
    (((MulAut.fixedResidualEquivOfCompatible 2 e a b heq) (d.symm x)).val)) = e x.val
  exact (MulAut.fixedResidualEquivOfCompatible_apply 2 e a b heq (d.symm x)).trans
    (congrArg e hx)


end CFSG.Quasithin.Chapter16.LiePreliminaries
