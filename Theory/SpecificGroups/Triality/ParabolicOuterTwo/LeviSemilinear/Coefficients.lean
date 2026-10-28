module

public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Actions
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootFrame
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Coefficient actions through the original triality Levi identifications

Transvection generation forces the coefficient action to commute with each
pinned SL₂ map. Coefficients commute with q-Frobenius, so this passes to the
three-arm fixed diagonal. At the central vertex the coefficient automorphism
is restricted to the actual fixed field and transported through the original
base-field equivalence. Descending these formulas through the elementary
central quotient and the original Levi projection gives equivariance for the
literal quotients by their intrinsic two-cores.

The trace test for PSL₂ field automorphisms then detects inner coefficient
actions: the full cubic coefficient is trivial on the arms, whereas only its
restriction to the fixed field is trivial at the central vertex.

Sources: GLS3 §§2.4–2.6, especially 2.5.12(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith F.1.12, printed pp.263–264,
`refs/quasithin.pdf`. All assertions include the binary endpoint.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.ParabolicOuterTwo
open Parabolics OuterOdd

private theorem map_transvection {F K : Type*} [Field F] [Field K]
    (f : F →+* K) {i j : Fin 2} (hij : i ≠ j) (t : F) :
    SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (f t) := by
  apply Subtype.ext
  change Matrix.map (1 + Matrix.single i j t) f = 1 + Matrix.single i j (f t)
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add]
  split_ifs <;> simp only [map_one, map_zero]

private theorem coefficient_pinned (P : Parameters) (D : PinnedRankOneMaps P)
    (e : CoefficientAut P) (i : Fin 4) (g : SL(2, ExtensionField P)) :
    coefficientSplit P e (D.hom i g) =
      D.hom i (SpecialLinearGroup.map e.toRingHom g) := by
  apply sl2_root_induction (fun g => coefficientSplit P e (D.hom i g) =
    D.hom i (SpecialLinearGroup.map e.toRingHom g)) ?_ ?_ ?_ g
  · intro t
    exact (congrArg (coefficientSplit P e) (D.positive i t)).trans
      ((coefficient_positiveRoot P e i t).trans
        ((D.positive i (e t)).symm.trans
          (congrArg (D.hom i) (map_transvection e.toRingHom (by decide : (0 : Fin 2) ≠ 1) t).symm)))
  · intro t
    exact (congrArg (coefficientSplit P e) (D.negative i t)).trans
      ((coefficient_negativeRoot P e i t).trans
        ((D.negative i (e t)).symm.trans
          (congrArg (D.hom i) (map_transvection e.toRingHom (by decide : (1 : Fin 2) ≠ 0) t).symm)))
  · intro g h hg hh
    simp only [map_mul, hg, hh]

private theorem coefficient_armsEmbedding (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (e : CoefficientAut P) (g : SL(2, ExtensionField P)) :
    coefficientSplit P e (D.armsFixedEmbedding C g) =
      D.armsFixedEmbedding C (SpecialLinearGroup.map e.toRingHom g) := by
  have hF (g : SL(2, ExtensionField P)) :
      SpecialLinearGroup.map e.toRingHom (sl2Frobenius P g) =
        sl2Frobenius P (SpecialLinearGroup.map e.toRingHom g) := by
    ext i j
    exact Coverage.coefficient_frobenius P e (g i j)
  change coefficientSplit P e
      (D.hom 0 g * D.hom 2 (sl2Frobenius P g) *
        D.hom 3 (sl2Frobenius P (sl2Frobenius P g))) = _
  simp only [map_mul, coefficient_pinned, hF]
  rfl

def coefficientBaseField (P : Parameters) (e : CoefficientAut P) :
    GaloisField P.prime P.exponent ≃+* GaloisField P.prime P.exponent :=
  ((baseFieldEquivFixed P).trans (Coverage.coefficientFixedField P e)).trans
    (baseFieldEquivFixed P).symm

theorem coefficientBaseField_embedding (P : Parameters) (e : CoefficientAut P)
    (t : GaloisField P.prime P.exponent) :
    baseFieldEmbedding P (coefficientBaseField P e t) = e (baseFieldEmbedding P t) := by
  exact congrArg Subtype.val ((baseFieldEquivFixed P).apply_symm_apply
    (Coverage.coefficientFixedField P e (baseFieldEquivFixed P t)))

private theorem coefficient_centralEmbedding (P : Parameters) (D : PinnedRankOneMaps P)
    (e : CoefficientAut P) (g : SL(2, GaloisField P.prime P.exponent)) :
    coefficientSplit P e (D.centralFixedEmbedding g) =
      D.centralFixedEmbedding (SpecialLinearGroup.map (coefficientBaseField P e).toRingHom g) := by
  change coefficientSplit P e (D.hom 1 (sl2BaseEmbedding P g)) = _
  rw [coefficient_pinned]
  apply congrArg (D.hom 1)
  ext i j
  exact (coefficientBaseField_embedding P e (g i j)).symm

private theorem embedding_equivariance {F : Type*} [Field F] [CharP F 2]
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (f : SL(2, F) →* SplitGroup P) (hf : Function.Injective f)
    (hr : f.range = splitLevi P a ⊓ fixedSubgroup P)
    (e : CoefficientAut P) (eF : F ≃+* F)
    (he : ∀ g, coefficientSplit P e (f g) = f (SpecialLinearGroup.map eF.toRingHom g))
    (x : levi P a) :
    leviEquivPSL2OfFixedEmbedding P a hp f hf hr (coefficientLevi P e a x) =
      Theory.PSL2.fieldAut eF (leviEquivPSL2OfFixedEmbedding P a hp f hf hr x) := by
  let E := leviEquivPSL2OfFixedEmbedding P a hp f hf hr
  let Q := Theory.PSL2.sl2QuotientEquiv F
  obtain ⟨g, hg⟩ := Q.surjective (E x)
  have hx : x = E.symm (Q g) := E.injective (by rw [E.apply_symm_apply, hg])
  rw [hx]
  change E (coefficientLevi P e a (E.symm (Q g))) = Theory.PSL2.fieldAut eF (E (E.symm (Q g)))
  rw [E.apply_symm_apply]
  change E (coefficientLevi P e a (E.symm (Q g))) =
    Theory.PSL2.fieldAut eF (Theory.PSL2.quotientMap F g)
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  apply E.symm.injective
  rw [E.symm_apply_apply]
  apply Subtype.ext
  have hval (g : SL(2, F)) :
      ((E.symm (Q g) : levi P a) : Carrier P) =
        toCarrier P (sl2ElementaryLift P hp
          (f.codRestrict (fixedSubgroup P) (fun g => (hr.le ⟨g, rfl⟩).2)) g) := by
    change toCarrier P (sl2ElementaryLift P hp
      (f.codRestrict (fixedSubgroup P) (fun g => (hr.le ⟨g, rfl⟩).2))
        (Q.symm (Q g))) = _
    exact congrArg (fun z => toCarrier P (sl2ElementaryLift P hp
      (f.codRestrict (fixedSubgroup P) (fun g => (hr.le ⟨g, rfl⟩).2)) z))
        (Q.symm_apply_apply g)
  change coefficientCarrier P e (E.symm (Q g)).val =
    (E.symm (Q (SpecialLinearGroup.map eF.toRingHom g))).val
  let f₀ := f.codRestrict (fixedSubgroup P) (fun g => (hr.le ⟨g, rfl⟩).2)
  have hlift : coefficientElementary P e (sl2ElementaryLift P hp f₀ g) =
      sl2ElementaryLift P hp f₀ (SpecialLinearGroup.map eF.toRingHom g) :=
    Subtype.ext (Subtype.ext (he g))
  exact (congrArg (coefficientCarrier P e) (hval g)).trans
    ((coefficientCarrier_toCarrier P e (sl2ElementaryLift P hp f₀ g)).trans
      ((congrArg (toCarrier P) hlift).trans
        (hval (SpecialLinearGroup.map eF.toRingHom g)).symm))

theorem coefficientLevi_arms (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (x : levi P .arms) :
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
    leviArmsEquivPSL2 P hp (coefficientLevi P e .arms x) =
      Theory.PSL2.fieldAut e (leviArmsEquivPSL2 P hp x) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  exact embedding_equivariance P hp .arms _
    ((pinnedRankOneMaps P hp).armsFixedEmbedding_injective (armRootCommutation P hp))
    ((pinnedRankOneMaps P hp).range_armsFixedEmbedding (armRootCommutation P hp)) e e
    (coefficient_armsEmbedding P (pinnedRankOneMaps P hp) (armRootCommutation P hp) e) x

theorem coefficientLevi_central (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (x : levi P .central) :
    let : CharP (GaloisField P.prime P.exponent) 2 :=
      hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
    leviCentralEquivPSL2 P hp (coefficientLevi P e .central x) =
      Theory.PSL2.fieldAut (coefficientBaseField P e) (leviCentralEquivPSL2 P hp x) := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  exact embedding_equivariance P hp .central _
    (pinnedRankOneMaps P hp).centralFixedEmbedding_injective
    (pinnedRankOneMaps P hp).range_centralFixedEmbedding e (coefficientBaseField P e)
    (coefficient_centralEmbedding P (pinnedRankOneMaps P hp) e) x

theorem coefficientLocalTwoQuotient_arms (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (x : LocalTwoQuotient P .arms) :
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
    localFactorArmsQuotientEquivPSL2 P hp (coefficientLocalTwoQuotient P e .arms x) =
      Theory.PSL2.fieldAut e (localFactorArmsQuotientEquivPSL2 P hp x) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  change leviArmsEquivPSL2 P hp
    (localFactorQuotientEquivLevi P hp .arms (coefficientLocalTwoQuotient P e .arms x)) = _
  rw [coefficientLocalTwoQuotient_equivLevi]
  exact coefficientLevi_arms P hp e _

theorem coefficientLocalTwoQuotient_central (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (x : LocalTwoQuotient P .central) :
    let : CharP (GaloisField P.prime P.exponent) 2 :=
      hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
    localFactorCentralQuotientEquivPSL2 P hp (coefficientLocalTwoQuotient P e .central x) =
      Theory.PSL2.fieldAut (coefficientBaseField P e)
        (localFactorCentralQuotientEquivPSL2 P hp x) := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  change leviCentralEquivPSL2 P hp
    (localFactorQuotientEquivLevi P hp .central (coefficientLocalTwoQuotient P e .central x)) = _
  rw [coefficientLocalTwoQuotient_equivLevi]
  exact coefficientLevi_central P hp e _

private theorem inner_field_of_equivariant {G F : Type*} [Group G] [Field F] [CharP F 2]
    (E : G ≃* Theory.PSL2.Group F) (a : MulAut G) (e : F ≃+* F)
    (he : ∀ x, E (a x) = Theory.PSL2.fieldAut e (E x))
    (ha : a ∈ MulAut.innerSubgroup G) : e = 1 := by
  obtain ⟨g, hg⟩ := ha
  apply Theory.PSL2.fieldAut_eq_conj_implies_refl e (E g)
  ext x
  obtain ⟨y, rfl⟩ := E.surjective x
  rw [← he, ← hg]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem coefficient_eq_one_of_arms_inner (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P)
    (h : coefficientLocalTwoQuotient P e .arms ∈
      MulAut.innerSubgroup (LocalTwoQuotient P .arms)) : e = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  exact inner_field_of_equivariant (localFactorArmsQuotientEquivPSL2 P hp) _ e
    (coefficientLocalTwoQuotient_arms P hp e) h

theorem coefficient_fixes_fixedField_of_central_inner (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P)
    (h : coefficientLocalTwoQuotient P e .central ∈
      MulAut.innerSubgroup (LocalTwoQuotient P .central)) :
    ∀ t : fixedField P, e t.val = t.val := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  have hb : coefficientBaseField P e = 1 :=
    inner_field_of_equivariant (localFactorCentralQuotientEquivPSL2 P hp) _ _
      (coefficientLocalTwoQuotient_central P hp e) h
  intro t
  obtain ⟨u, rfl⟩ := (baseFieldEquivFixed P).surjective t
  have hu := coefficientBaseField_embedding P e u
  rw [hb] at hu
  exact hu.symm

end Triality.Standard.ParabolicOuterTwo
