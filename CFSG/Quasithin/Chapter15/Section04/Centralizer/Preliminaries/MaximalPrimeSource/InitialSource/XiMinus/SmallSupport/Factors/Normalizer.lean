module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Factors.Enumeration
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupAction.SupportEquivalence

/-!
# Normalizer equivariance of the canonical Frattini factors

The original Frattini projection identifies the odd image P with the
Frattini quotient of X. Transport the original X-normalizer action along
that map. For an element also normalizing the original module V, its
conjugation on V is compatible with this transported action on P.
Action-support transport therefore preserves the defining conditions of
the canonical five-factors. Since there are exactly two, their literal
Frattini images are preserved or interchanged.

No normalization of T or XT, prescribed decomposition, or factor
permutation is assumed. The full-normalizer conclusion is assembled
separately through the normalizer of O₂(XT).
Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
universe u
variable {G : Type u} [Group G] {T X : Subgroup G}

/-- Conjugation on the literal module, transferred through its embedding in G. -/
@[expose] noncomputable def sourceModuleNormalizerAut
    (n : normalizer (X : Set G))
    (hnV : (n : G) ∈ normalizer
      ((sourceModule T X).map (sourceGroup T X).subtype : Set G)) :
    MulAut (Multiplicative (Additive (sourceModule T X))) :=
  let eV := (sourceModule T X).equivMapOfInjective
    (sourceGroup T X).subtype (sourceGroup T X).subtype_injective
  AddEquiv.toMultiplicative (MulEquiv.toAdditive
    ((eV.trans (((sourceModule T X).map (sourceGroup T X).subtype).normalizerMonoidHom
      ⟨(n : G), hnV⟩)).trans eV.symm))

theorem sourceModuleNormalizerAut_apply
    (n : normalizer (X : Set G))
    (hnV : (n : G) ∈ normalizer
      ((sourceModule T X).map (sourceGroup T X).subtype : Set G))
    (w : Multiplicative (Additive (sourceModule T X))) :
    (((sourceModuleNormalizerAut n hnV w).toAdd.toMul : sourceGroup T X) : G) =
      (n : G) * ((w.toAdd.toMul : sourceGroup T X) : G) * (n : G)⁻¹ := by
  let J := sourceGroup T X
  let U := sourceModule T X
  let eV := U.equivMapOfInjective J.subtype J.subtype_injective
  let b := (U.map J.subtype).normalizerMonoidHom ⟨(n : G), hnV⟩
  have hh := congrArg (fun z : U.map J.subtype => (z : G))
    (eV.apply_symm_apply (b (eV w.toAdd.toMul)))
  change (((eV.symm (b (eV w.toAdd.toMul)) : U) : J) : G) = _
  simpa only [eV, b, coe_equivMapOfInjective_apply,
    normalizerMonoidHom_apply_apply_coe, Subgroup.subtype_apply] using hh

theorem sourceOddProjection_smul_coe (hX : X ∈ Chapter1.Xi G T)
    (x : X) (w : Multiplicative (Additive (sourceModule T X))) :
    let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
    ((((sourceOddProjection hX x) • w).toAdd.toMul : sourceGroup T X) : G) =
      (x : G) * ((w.toAdd.toMul : sourceGroup T X) : G) * (x : G)⁻¹ := by
  dsimp only
  let := sourceModule_normal hX
  have hh := congrArg (fun j : sourceGroup T X => (j : G))
    (Representation.NormalElementaryQuotient.representation_apply (sourceModule T X)
      (sourceActionProjection hX) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (inclusion (show X ≤ sourceGroup T X from le_sup_left) x) w.toAdd)
  exact hh

variable [Finite G]

/-- The original Frattini projection is an isomorphism in the five-group case. -/
@[expose] noncomputable def sourceFrattiniEquiv (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    sourceOddImage hX ≃* Chapter1.XiFrattiniQuotient X :=
  MulEquiv.ofBijective (sourceFrattiniProjection hX hk)
    ⟨sourceFrattiniProjection_injective hX hT hred hk hratio hp,
      sourceFrattiniProjection_surjective hX hk⟩

/-- The original X-normalizer action transported along the actual Frattini projection. -/
@[expose] noncomputable def sourceNormalizerOddAut (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X))
    (n : normalizer (X : Set G)) : MulAut (sourceOddImage hX) :=
  let e := sourceFrattiniEquiv hX hT hred hk hratio hp
  (e.trans (quotientAut (frattini (Chapter1.XiQuotient X))
    (Chapter3.xiQuotientNormalizerAction X n))).trans e.symm

theorem sourceNormalizerOddAut_apply_projection (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X))
    (n : normalizer (X : Set G)) (x : X) :
    sourceNormalizerOddAut hX hT hred hk hratio hp n (sourceOddProjection hX x) =
      sourceOddProjection hX (X.normalizerMonoidHom n x) := by
  let e := sourceFrattiniEquiv hX hT hred hk hratio hp
  apply e.injective
  change e (e.symm (quotientAut (frattini (Chapter1.XiQuotient X))
    (Chapter3.xiQuotientNormalizerAction X n) (e (sourceOddProjection hX x)))) = _
  rw [e.apply_symm_apply]
  change quotientAut (frattini (Chapter1.XiQuotient X))
    (Chapter3.xiQuotientNormalizerAction X n)
      (sourceFrattiniProjection hX hk (sourceOddProjection hX x)) =
    sourceFrattiniProjection hX hk (sourceOddProjection hX (X.normalizerMonoidHom n x))
  rw [sourceFrattiniProjection_apply, sourceFrattiniProjection_apply,
    quotientAut_apply_mk]
  change QuotientGroup.mk' _ (quotientAut (pCore 2 X) (X.normalizerMonoidHom n)
    (QuotientGroup.mk' _ x)) = _
  rw [quotientAut_apply_mk]

theorem sourceNormalizer_compatible (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X))
    (n : normalizer (X : Set G))
    (hnV : (n : G) ∈ normalizer
      ((sourceModule T X).map (sourceGroup T X).subtype : Set G)) :
    let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
    ∀ p : sourceOddImage hX, ∀ w : Multiplicative (Additive (sourceModule T X)),
      sourceModuleNormalizerAut n hnV (p • w) =
        sourceNormalizerOddAut hX hT hred hk hratio hp n p • sourceModuleNormalizerAut n hnV w := by
  dsimp only
  let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
  intro p w
  obtain ⟨x, rfl⟩ := sourceOddProjection_surjective hX p
  rw [sourceNormalizerOddAut_apply_projection]
  change (sourceModuleNormalizerAut n hnV ((sourceOddProjection hX x) • w)).toAdd.toMul =
    ((sourceOddProjection hX (X.normalizerMonoidHom n x)) •
      sourceModuleNormalizerAut n hnV w).toAdd.toMul
  apply Subtype.ext
  apply Subtype.ext
  simp only [sourceModuleNormalizerAut_apply, sourceOddProjection_smul_coe,
    normalizerMonoidHom_apply_apply_coe]
  group

theorem sourceNormalizerOddAut_frattini (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X))
    (n : normalizer (X : Set G)) (p : sourceOddImage hX) :
    sourceFrattiniProjection hX hk (sourceNormalizerOddAut hX hT hred hk hratio hp n p) =
      quotientAut (frattini (Chapter1.XiQuotient X))
        (Chapter3.xiQuotientNormalizerAction X n) (sourceFrattiniProjection hX hk p) := by
  let e := sourceFrattiniEquiv hX hT hred hk hratio hp
  exact e.apply_symm_apply _

/-- Simultaneous normalization of X and its module preserves the canonical five-factors. -/
theorem sourceNormalizer_preserves_factors (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X))
    (n : normalizer (X : Set G))
    (hnV : (n : G) ∈ normalizer
      ((sourceModule T X).map (sourceGroup T X).subtype : Set G))
    {D : Subgroup (sourceActionGroup hX)} (hD : D ∈ sourceFiveFactors hX) :
    (((D.subgroupOf (sourceOddImage hX)).map
      (sourceNormalizerOddAut hX hT hred hk hratio hp n).toMonoidHom).map
        (sourceOddImage hX).subtype) ∈ sourceFiveFactors hX := by
  let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
  let P := sourceOddImage hX
  let W := Multiplicative (Additive (sourceModule T X))
  let a := sourceNormalizerOddAut hX hT hred hk hratio hp n
  let b := sourceModuleNormalizerAut n hnV
  have hDP : D ≤ P := (le_sSup hD).trans
    (sourceFiveGroup_eq_oddImage hX hT hred hk hratio hp).le
  have hPF : P ≤ fittingSubgroup (sourceActionGroup hX) := by
    rw [show P = pCore 5 (sourceActionGroup hX) from
      sourceOddImage_eq_pCore hX hT (by decide : Odd 5) hp]
    exact pCore_le_fitting _ 5
  refine ⟨(map_subtype_le _).trans hPF, ?_, ?_⟩
  · rw [card_map_of_injective P.subtype_injective, card_map_of_injective a.injective,
      Nat.card_congr (subgroupOfEquivOfLe hDP).toEquiv]
    exact hD.2.1
  · have hh := ActionSupport.equiv_commutatorAction a b
      (sourceNormalizer_compatible hX hT hred hk hratio hp n hnV) (D.subgroupOf P)
    rw [← commutatorAction_map_actor_subtype P (D.subgroupOf P),
      map_subgroupOf_eq_of_le hDP] at hh
    rw [commutatorAction_map_actor_subtype, ← hh,
      card_map_of_injective (f := b.toMonoidHom) b.injective]
    exact hD.2.2

theorem sourceNormalizer_factor_frattini_image (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X))
    (n : normalizer (X : Set G)) (D : Subgroup (sourceActionGroup hX)) :
    let P := sourceOddImage hX
    let a := sourceNormalizerOddAut hX hT hred hk hratio hp n
    let f := sourceFrattiniProjection hX hk
    ((((D.subgroupOf P).map a.toMonoidHom).map P.subtype).subgroupOf P).map f =
      ((D.subgroupOf P).map f).map
        (quotientAut (frattini (Chapter1.XiQuotient X))
          (Chapter3.xiQuotientNormalizerAction X n)).toMonoidHom := by
  dsimp only
  rw [show (((D.subgroupOf (sourceOddImage hX)).map
      (sourceNormalizerOddAut hX hT hred hk hratio hp n).toMonoidHom).map
        (sourceOddImage hX).subtype).subgroupOf (sourceOddImage hX) =
      (D.subgroupOf (sourceOddImage hX)).map
        (sourceNormalizerOddAut hX hT hred hk hratio hp n).toMonoidHom from
      comap_map_eq_self_of_injective (sourceOddImage hX).subtype_injective _]
  rw [map_map, map_map]
  congr 1
  ext p
  exact sourceNormalizerOddAut_frattini hX hT hred hk hratio hp n p

/-- The two original Frattini factors are permuted by the normalizer of X and V. -/
theorem source_moduleNormalizer_frattini_pair (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    ∃ B E : Subgroup (Chapter1.XiFrattiniQuotient X),
      Nat.card B = 5 ∧ Nat.card E = 5 ∧ B ≠ E ∧ B ⊔ E = ⊤ ∧
      ∀ n : normalizer (X : Set G),
        (n : G) ∈ normalizer ((sourceModule T X).map (sourceGroup T X).subtype : Set G) →
        let f := quotientAut (frattini (Chapter1.XiQuotient X))
          (Chapter3.xiQuotientNormalizerAction X n)
        (B.map f.toMonoidHom = B ∧ E.map f.toMonoidHom = E) ∨
          (B.map f.toMonoidHom = E ∧ E.map f.toMonoidHom = B) := by
  obtain ⟨D, C, hD, hC, _, _, hfam, hB, hE, hne, hsup⟩ :=
    source_canonical_frattini_pair hX hT hred hk hratio hp
  let P := sourceOddImage hX
  let f := sourceFrattiniProjection hX hk
  let B := (D.subgroupOf P).map f
  let E := (C.subgroupOf P).map f
  refine ⟨B, E, hB, hE, hne, hsup, ?_⟩
  intro n hnV
  let a := sourceNormalizerOddAut hX hT hred hk hratio hp n
  let s := quotientAut (frattini (Chapter1.XiQuotient X))
    (Chapter3.xiQuotientNormalizerAction X n)
  have himage (K : Subgroup (sourceActionGroup hX)) (hK : K ∈ sourceFiveFactors hX) :
      ((K.subgroupOf P).map f).map s.toMonoidHom = B ∨
        ((K.subgroupOf P).map f).map s.toMonoidHom = E := by
    have hm := sourceNormalizer_preserves_factors hX hT hred hk hratio hp n hnV hK
    rw [hfam] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    have hh := sourceNormalizer_factor_frattini_image hX hT hred hk hratio hp n K
    dsimp only at hh
    rcases hm with he | he
    · rw [he] at hh
      exact Or.inl hh.symm
    · rw [he] at hh
      exact Or.inr hh.symm
  rcases himage D hD with hDB | hDE <;> rcases himage C hC with hCB | hCE
  · exact (hne ((map_injective s.injective) (hDB.trans hCB.symm))).elim
  · exact Or.inl ⟨hDB, hCE⟩
  · exact Or.inr ⟨hDE, hCB⟩
  · exact (hne ((map_injective s.injective) (hDE.trans hCE.symm))).elim

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
