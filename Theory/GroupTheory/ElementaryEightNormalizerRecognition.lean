module

public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Recognizing an elementary order-eight normalizer image and quotient

Let `U` be an elementary abelian subgroup of order eight in a finite group.
If the actual conjugation image of its normalizer contains two distinct
subgroups isomorphic to S₄, the normalizer is not solvable. This conclusion
needs no self-centralization or faithfulness assumption. If `U` is additionally
self-centralizing and the actual normalizer quotient by `U` contains two
distinct S₄ subgroups, that quotient is isomorphic to PSL₃(2). These independent
normalizer-recognition results support Stellmacher (9.1)(c), Journal of Algebra
190 (1997), p. 48; no campaign hypotheses or imports are needed.

The conjugation range includes injectively into Aut(U), which the shared
elementary-group results identify with GL₃(2) and count as 168. An order-24
subgroup has prime index seven. If the range were proper, both S₄ images would
equal it, contradicting distinctness. GL₃(2) is SL₃(2), since F₂ has only one
unit, and the scalar description of the SL center makes that center trivial.
Thus the range is PSL₃(2), whose intrinsic nonsolvability is proved in
`Theory.SpecificGroups.PSL3Two.NonSolvable`. Solvability descends through the
surjective range restriction, giving the kernel-free contradiction.

The general centralizer-quotient endpoint composes the actual conjugation
range restriction with this PSL3 equivalence. Its kernel is exactly the
ambient centralizer restricted to the normalizer, without self-centralization.
It supplies the normalizer quotient in Stellmacher (8.6)(c4), printed p.44.

For the self-centralizing quotient result, self-centralization identifies the conjugation kernel
with `U` inside its normalizer. The first isomorphism theorem then embeds the
quotient into Aut(U), and the same order and linear-model arguments identify
it with the concrete projective special linear group.
-/

universe u

private noncomputable def glThreeTwoEquivPSL :
    Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) := by
  have hunits : ∀ unit : (ZMod 2)ˣ, unit = 1 := by decide
  have hsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →*
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
    intro mat
    have hdet : Matrix.det (mat : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
      exact congrArg Units.val (hunits (Matrix.GeneralLinearGroup.det mat))
    exact ⟨⟨mat, hdet⟩, Units.ext rfl⟩
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro mat hmat
    change mat = 1
    obtain ⟨scalar, hpower, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmat
    have hscalarOne : scalar = 1 := by
      have hroot : ∀ scalar : ZMod 2, scalar ^ 3 = 1 → scalar = 1 := by decide
      exact hroot scalar (by simpa using hpower)
    apply Subtype.ext
    simpa [hscalarOne] using hscalar.symm
  exact (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, hsurj⟩).symm.trans
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcenter.symm))

private theorem surjective_of_two_symmetric_four
    {G A : Type*} [Group G] [Group A] [Finite A]
    (hom : G →* A) (hinj : Function.Injective hom) (hcard : Nat.card A = 168)
    (X Y : Subgroup G) (hne : X ≠ Y)
    (hX : Nonempty (X ≃* Equiv.Perm (Fin 4)))
    (hY : Nonempty (Y ≃* Equiv.Perm (Fin 4))) :
    Function.Surjective hom := by
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hXcard : Nat.card (X.map hom) = 24 := by
    rw [Subgroup.card_map_of_injective hinj, Nat.card_congr hX.some.toEquiv, hperm]
  have hYcard : Nat.card (Y.map hom) = 24 := by
    rw [Subgroup.card_map_of_injective hinj, Nat.card_congr hY.some.toEquiv, hperm]
  have hXindex : (X.map hom).index = 7 := by
    have hmul := (X.map hom).card_mul_index
    rw [hXcard, hcard] at hmul
    omega
  have hrange : hom.range.index ∣ 7 := by
    rw [← hXindex]
    exact Subgroup.index_dvd_of_le (X.map_le_range hom)
  rcases (show Nat.Prime 7 by decide).eq_one_or_self_of_dvd _ hrange with htop | hseven
  · exact MonoidHom.range_eq_top.mp (Subgroup.index_eq_one.mp htop)
  · have hRcard : Nat.card hom.range = 24 := by
      have hmul := hom.range.card_mul_index
      rw [hseven, hcard] at hmul
      omega
    have hXR : X.map hom = hom.range :=
      Subgroup.eq_of_le_of_card_ge (X.map_le_range hom) (by omega)
    have hYR : Y.map hom = hom.range :=
      Subgroup.eq_of_le_of_card_ge (Y.map_le_range hom) (by omega)
    exact (hne (Subgroup.map_injective hinj (hXR.trans hYR.symm))).elim

/-- Two distinct S₄ subgroups in the actual conjugation image of an elementary
subgroup of order eight force its normalizer to be nonsolvable, without any
assumption on the conjugation kernel. -/
public theorem elementaryEight_normalizer_not_isSolvable_of_two_symmetric_four_images
    {H : Type u} [Group H] [Finite H] (U : Subgroup H)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (X Y : Subgroup U.normalizerMonoidHom.range) (hne : X ≠ Y)
    (hX : Nonempty (X ≃* Equiv.Perm (Fin 4)))
    (hY : Nonempty (Y ≃* Equiv.Perm (Fin 4))) :
    ¬ Group.IsSolvable (Subgroup.normalizer (U : Set H)) := by
  classical
  let hom := U.normalizerMonoidHom.range.subtype
  have hinj : Function.Injective hom := Subtype.val_injective
  have hsurj : Function.Surjective hom :=
    surjective_of_two_symmetric_four hom hinj
      (card_mulAut_of_elementary_eight U hU) X Y hne hX hY
  let rangeToPSL := (MulEquiv.ofBijective hom ⟨hinj, hsurj⟩).trans
    ((elementaryEight_mulAut_equiv_GL U hU).some.trans glThreeTwoEquivPSL)
  intro hsolvable
  have : Group.IsSolvable U.normalizerMonoidHom.range :=
    Group.isSolvable_of_surjective U.normalizerMonoidHom.rangeRestrict_surjective
  exact not_isSolvable_psl3_two
    (Group.isSolvable_of_surjective (f := rangeToPSL.toMonoidHom) rangeToPSL.surjective)

/-- Two distinct S₄ subgroups force the normalizer quotient of a
self-centralizing elementary subgroup of order eight to be PSL₃(2). -/
public theorem elementaryEight_normalizer_quotient_equiv_PSL3
    {H : Type u} [Group H] [Finite H] (U : Subgroup H)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hcentral : Subgroup.centralizer (U : Set H) = U)
    (X Y : Subgroup
      ((Subgroup.normalizer (U : Set H)) ⧸ U.subgroupOf (Subgroup.normalizer (U : Set H))))
    (hne : X ≠ Y)
    (hX : Nonempty (X ≃* Equiv.Perm (Fin 4)))
    (hY : Nonempty (Y ≃* Equiv.Perm (Fin 4))) :
    Nonempty (((Subgroup.normalizer (U : Set H)) ⧸
      U.subgroupOf (Subgroup.normalizer (U : Set H))) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  classical
  have hker : U.normalizerMonoidHom.ker =
      U.subgroupOf (Subgroup.normalizer (U : Set H)) := by
    rw [Subgroup.normalizerMonoidHom_ker, hcentral]
  let quotientToRange := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange U.normalizerMonoidHom)
  let hom := U.normalizerMonoidHom.range.subtype.comp quotientToRange.toMonoidHom
  have hinj : Function.Injective hom :=
    Subtype.val_injective.comp quotientToRange.injective
  have hsurj : Function.Surjective hom :=
    surjective_of_two_symmetric_four hom hinj
      (card_mulAut_of_elementary_eight U hU) X Y hne hX hY
  exact ⟨(MulEquiv.ofBijective hom ⟨hinj, hsurj⟩).trans
    ((elementaryEight_mulAut_equiv_GL U hU).some.trans glThreeTwoEquivPSL)⟩

/-- Full conjugation image recognizes the quotient by the actual centralizer,
without assuming that the elementary subgroup is self-centralizing. -/
public theorem elementaryEight_normalizer_centralizer_quotient_PSL3
    {H : Type u} [Group H] [Finite H] (U : Subgroup H)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (X Y : Subgroup U.normalizerMonoidHom.range) (hne : X ≠ Y)
    (hX : Nonempty (X ≃* Equiv.Perm (Fin 4)))
    (hY : Nonempty (Y ≃* Equiv.Perm (Fin 4))) :
    ∃ f : Subgroup.normalizer (U : Set H) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧
        f.ker = (Subgroup.centralizer (U : Set H)).subgroupOf
          (Subgroup.normalizer (U : Set H)) := by
  classical
  let hom := U.normalizerMonoidHom.range.subtype
  have hinj : Function.Injective hom := Subtype.val_injective
  have hsurj : Function.Surjective hom := surjective_of_two_symmetric_four hom hinj
    (card_mulAut_of_elementary_eight U hU) X Y hne hX hY
  let e := (MulEquiv.ofBijective hom ⟨hinj,hsurj⟩).trans
    ((elementaryEight_mulAut_equiv_GL U hU).some.trans glThreeTwoEquivPSL)
  let f := e.toMonoidHom.comp U.normalizerMonoidHom.rangeRestrict
  refine ⟨f,e.surjective.comp U.normalizerMonoidHom.rangeRestrict_surjective,?_⟩
  change (e.toMonoidHom.comp U.normalizerMonoidHom.rangeRestrict).ker = _
  have hk : (e.toMonoidHom.comp U.normalizerMonoidHom.rangeRestrict).ker =
      U.normalizerMonoidHom.rangeRestrict.ker := by
    ext a
    change e (U.normalizerMonoidHom.rangeRestrict a)=1 ↔
      U.normalizerMonoidHom.rangeRestrict a=1
    rw [← e.map_one]
    exact e.injective.eq_iff
  rw [hk,MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker]
