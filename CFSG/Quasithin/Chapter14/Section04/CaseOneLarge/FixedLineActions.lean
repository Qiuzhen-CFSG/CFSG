module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineModels
public import Theory.Alternating.IndexEightSubgroups
public import Theory.Representation.BinaryPermutation.FiveDoubleNormalizer
public import Theory.Representation.BinaryPermutation.SixDoubleNormalizer
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.Representation.AlternatingSevenConjugatePair.Model.OuterDual
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.SymplecticComparison.PolarModel

/-!
# Actual actions of the original marked fixed-line constituent

The previous carrier and degree sieve leaves A₅, A₆ and A₇ in dimension four.
A faithful A₇ four-space is recognized using the actual GL₄(2)–A₈ comparison
and conjugacy of index-eight subgroups. Its dual is the inequivalent outer
four-space, contradicting self-duality of the marked constituent. The complete
SL₂(4) and A₆ catalogues then identify the surviving constituent with the
natural SL₂(4) action or the deleted five- or six-point action.

The proved multiplicity two supplies compatible coordinates on the full
component restriction. For each permutation row, its actual tensor normalizer
extends these coordinates to a faithful embedding of the entire original
terminal group, retaining the component in the first factor. Finally select
an original moved component and homogeneous constituent: it either contains
the marked point and has these actions, or has the literal exchanged geometry.

These are constructed source reductions. Whole-group image identification,
recognition of exchanged constituents, and marked-catalogue exhaustion remain
open. In particular, a tensor-normalizer embedding is not asserted surjective.
The four-space coordinate proof adapts ChapterK's Seven/FourSpace directly,
using only faithfulness and the original A₇ marking; all model comparisons
retain the existing ATLAS attribution through their imports.
Source: Aschbacher--Smith G.11.6--8 and 14.4.2, printed pp.365--369,1006--1007;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups MonoidAlgebra TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
namespace FixedLineActions
open ChapterG.Section09
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
namespace Seven
open AlternatingSevenConjugatePair.Model
private def linearEquivToSL (e : Four ≃ₗ[ZMod 2] Four) : SL(4, ZMod 2) :=
  ⟨LinearMap.toMatrix' e.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ e.isUnit_det'.ne_zero⟩

private theorem linearEquivToSL_apply (e : Four ≃ₗ[ZMod 2] Four) :
    Matrix.SpecialLinearGroup.toLin' (linearEquivToSL e) = e := by
  apply LinearEquiv.toLinearMap_injective
  exact Matrix.toLin'_toMatrix' e.toLinearMap

private def linearEquivToSLHom : (Four ≃ₗ[ZMod 2] Four) →* SL(4, ZMod 2) where
  toFun := linearEquivToSL
  map_one' := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [linearEquivToSL_apply, map_one]
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_mul, linearEquivToSL_apply, linearEquivToSL_apply, linearEquivToSL_apply]

private def comparison : alternatingGroup (Fin 8) ≃* SL(4, ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    Atlas.Order20160A8.sl4TwoEquivPSL.symm

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private def coordinateAction (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : Representation (ZMod 2) G Four :=
  b.conjRingEquiv.toMonoidHom.comp ρ

private def linearImage (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : G →* SL(4, ZMod 2) :=
  linearEquivToSLHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Four).toMonoidHom.comp
      (coordinateAction ρ b).asGroupHom)

private theorem linearImage_apply (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (g : G) (v : V) :
    Matrix.SpecialLinearGroup.toLin' (linearImage ρ b g) (b v) = b (ρ g v) := by
  rw [show linearImage ρ b g = linearEquivToSL
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Four
      ((coordinateAction ρ b).asGroupHom g)) from rfl, linearEquivToSL_apply]
  change b (ρ g (b.symm (b v))) = _
  rw [b.symm_apply_apply]

private theorem linearImage_injective (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (hf : Function.Injective ρ) :
    Function.Injective (linearImage ρ b) := by
  intro g h he
  apply hf
  ext v
  apply b.injective
  rw [← linearImage_apply ρ b g, ← linearImage_apply ρ b h, he]

private def permutationImage (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : G →* alternatingGroup (Fin 8) :=
  comparison.symm.toMonoidHom.comp (linearImage ρ b)

private theorem permutationImage_injective (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (hf : Function.Injective ρ) :
    Function.Injective (permutationImage ρ b) :=
  comparison.symm.injective.comp (linearImage_injective ρ b hf)



private theorem four_coordinates [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfρ : Function.Injective ρ)
    (eG : G ≃* alternatingGroup (Fin 7)) (hd : finrank (ZMod 2) V = 4) :
    Quasiequivalent ρ natural := by
  classical
  obtain ⟨b⟩ : Nonempty (V ≃ₗ[ZMod 2] Four) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hd.trans four_dimension.symm)
  let f := permutationImage ρ b
  have hf : Function.Injective f := permutationImage_injective ρ b hfρ
  let H := f.range
  have hcard : Nat.card H = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr eG.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hindex : H.index = 8 := by
    have hh := H.card_mul_index
    rw [hcard, hA] at hh
    omega
  let J := alternatingEmbedding.range
  have hJcard : Nat.card J = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective alternatingEmbedding_injective).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hJindex : J.index = 8 := by
    have hh := J.card_mul_index
    rw [hJcard, hA] at hh
    omega
  -- Conjugacy takes place inside A₈, so it lifts to a linear coordinate change.
  obtain ⟨c, hc⟩ := GroupTheory.AlternatingIndexEight.index_eight_conjugate
    H J hindex hJindex
  let q := (MulAut.conj c).toMonoidHom.comp f
  have hq : Function.Injective q := (MulAut.conj c).injective.comp
    hf
  have hqr : q.range = alternatingEmbedding.range := by
    rw [MonoidHom.range_comp]
    exact hc
  let eGroup : G ≃* alternatingGroup (Fin 7) :=
    (MonoidHom.ofInjective hq).trans ((MulEquiv.subgroupCongr hqr).trans
      (MonoidHom.ofInjective alternatingEmbedding_injective).symm)
  have he (l : G) : alternatingEmbedding (eGroup l) = q l := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective alternatingEmbedding_injective).apply_symm_apply
        ((MulEquiv.subgroupCongr hqr) ((MonoidHom.ofInjective hq) l)))
  let t : Four ≃ₗ[ZMod 2] Four := Matrix.SpecialLinearGroup.toLin' (comparison c)
  refine ⟨eGroup, b.trans t, fun l v => ?_⟩
  have hlin : linearEmbedding (eGroup l) =
      comparison c * linearImage ρ b l * (comparison c)⁻¹ := by
    change comparison (alternatingEmbedding (eGroup l)) = _
    rw [he]
    change comparison (c * (comparison.symm (linearImage ρ b l)) * c⁻¹) = _
    rw [map_mul, map_mul, map_inv, comparison.apply_symm_apply]
  change t (b (ρ l v)) =
    Matrix.SpecialLinearGroup.toLin' (linearEmbedding (eGroup l)) (t (b v))
  rw [hlin, map_mul, map_mul, map_inv]
  change t (b (ρ l v)) = t
    (Matrix.SpecialLinearGroup.toLin' (linearImage ρ b l) (t.symm (t (b v))))
  rw [t.symm_apply_apply, linearImage_apply]


private theorem no_selfDual [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (eG : G ≃* alternatingGroup (Fin 7)) (hd : finrank (ZMod 2) V = 4)
    (hs : Nonempty (ρ.Equiv ρ.dual)) : False := by
  obtain ⟨e,c,hc⟩ := four_coordinates ρ hf eG hd
  obtain ⟨d⟩ := hs
  let f : natural.Equiv natural.dual := .mk
    ((c.symm.trans d.toLinearEquiv).trans c.symm.dualMap) (by
      intro a
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro w
      have hi (b : alternatingGroup (Fin 7)) (z : Four) :
          c.symm (natural b z) = ρ (e.symm b) (c.symm z) := by
        apply c.injective
        rw [c.apply_symm_apply,hc,e.apply_symm_apply,c.apply_symm_apply]
      change d (c.symm (natural a u)) (c.symm w) =
        d (c.symm u) (c.symm (natural a⁻¹ w))
      rw [hi,hi]
      have hh := congrArg (fun q : Module.Dual (ZMod 2) V => q (c.symm w))
        (Representation.IntertwiningMap.isIntertwining ρ ρ.dual
          d.toIntertwiningMap (e.symm a) (c.symm u))
      simpa only [Representation.Equiv.coe_toIntertwiningMap,
        Representation.dual_apply, Module.Dual.transpose_apply,
        LinearMap.comp_apply, e.symm.map_inv] using hh)
  exact natural_not_equiv_outerNatural ⟨f.trans outerDualEquiv.symm⟩
end Seven

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Concrete faithful four-space models, with both actor and module equivalences. -/
@[expose] def Models (ρ : Representation (ZMod 2) D W) : Prop :=
  Quasiequivalent ρ (SL2.BinarySmall.natural (K := OrthogonalFourMinus.FiniteModel.Field 1)) ∨
  Quasiequivalent ρ (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) ∨
  Quasiequivalent ρ (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))

omit [Finite D] in
private theorem five_models (ρ : Representation (ZMod 2) D W)
    [IsIrreducible ρ] (hf : Function.Injective ρ)
    (e : D ≃* alternatingGroup (Fin 5)) : Models ρ := by
  let : Nontrivial D := e.symm.injective.nontrivial
  obtain ⟨a,ha⟩ := exists_ne (1 : D)
  have hn : ∃ g, ρ g ≠ 1 := ⟨a,fun he => ha (hf (he.trans ρ.map_one.symm))⟩
  obtain ⟨_,h | h⟩ :=
    ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives ρ e hn
  · obtain ⟨f,⟨c⟩⟩ := h
    exact Or.inl ⟨f,c.toLinearEquiv,fun b w => LinearMap.congr_fun (c.isIntertwining' b) w⟩
  · obtain ⟨f,⟨c⟩⟩ := h
    exact Or.inr (Or.inl ⟨f,c.toLinearEquiv,fun b w => LinearMap.congr_fun (c.isIntertwining' b) w⟩)

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem six_permutation_coordinates (ρ : Representation (ZMod 2) D W)
    (hm : Quasiequivalent ρ BinaryAlternatingSix.firstAlternating) :
    Quasiequivalent ρ (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) := by
  obtain ⟨e,c,hc⟩ := hm
  let d := HexadSymplecticComparison.PolarModel.deletedToPolar
  have hd (a : alternatingGroup (Fin 6)) (w : BinaryPermutation.natural (Fin 6)) :
      d (BinaryPermutation.alternatingNaturalRepresentation (Fin 6) a w) =
        BinaryAlternatingSix.firstAlternating a (d w) :=
    (HexadSymplecticComparison.PolarModel.deletedToPolar_equivariant a w).trans
      (Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply a (d w))
  refine ⟨e,c.trans d.symm,?_⟩
  intro a w
  apply d.injective
  change d (d.symm (c (ρ a w))) =
    d (BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (e a) (d.symm (c w)))
  rw [d.apply_symm_apply,hd,d.apply_symm_apply,hc]

omit [Finite D] in
private theorem six_models (ρ : Representation (ZMod 2) D W)
    [IsIrreducible ρ] (hd : finrank (ZMod 2) W = 4)
    (e : D ≃* alternatingGroup (Fin 6)) : Models ρ := by
  let σ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr inferInstance
  rcases BinaryAlternatingSix.alternating_classify σ with h | h | h | h
  · obtain ⟨c⟩ := h
    have he := c.toLinearEquiv.finrank_eq
    change finrank (ZMod 2) W = finrank (ZMod 2) (ZMod 2) at he
    rw [Module.finrank_self] at he
    omega
  · obtain ⟨c⟩ := h
    refine Or.inr (Or.inr (six_permutation_coordinates ρ ⟨e,c.toLinearEquiv,?_⟩))
    intro b w
    simpa [σ, BinaryAlternatingSix.secondNatural] using LinearMap.congr_fun (c.isIntertwining' (e b)) w
  · obtain ⟨c⟩ := h
    refine Or.inr (Or.inr (six_permutation_coordinates ρ
      ⟨e.trans BinaryAlternatingSix.alternatingDiagramAut,c.toLinearEquiv,?_⟩))
    intro b w
    simpa [σ, BinaryAlternatingSix.secondNatural] using LinearMap.congr_fun (c.isIntertwining' (e b)) w
  · obtain ⟨c⟩ := h
    have he := c.toLinearEquiv.finrank_eq
    rw [BinaryAlternatingSix.tensor_finrank] at he
    omega

/-- The three actual doubled component actions in the marked fixed-line branch. -/
@[expose] def DoubledModels (ρ : Representation (ZMod 2) D W) : Prop :=
  let N := SL2.BinarySmall.natural (K := OrthogonalFourMinus.FiniteModel.Field 1)
  let A := BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
  let S := BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
  Quasiequivalent ρ (N.prod N) ∨ Quasiequivalent ρ (A.prod A) ∨
    Quasiequivalent ρ (S.prod S)

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem double_coordinates
    {E U V : Type*} [Group E] [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D W) (R : Representation (ZMod 2) D U)
    (σ : Representation (ZMod 2) E V)
    (d : ρ.Equiv (R.prod R)) (hm : Quasiequivalent R σ) :
    Quasiequivalent ρ (σ.prod σ) := by
  obtain ⟨e,c,hc⟩ := hm
  refine ⟨e,d.toLinearEquiv.trans (c.prodCongr c),?_⟩
  intro a w
  have hh := LinearMap.congr_fun (d.isIntertwining' a) w
  change d (ρ a w) = (R a (d w).1,R a (d w).2) at hh
  change (c (d (ρ a w)).1,c (d (ρ a w)).2) = _
  rw [hh,hc,hc]
  rfl

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem doubled_models
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) D W) (R : Representation (ZMod 2) D U)
    (d : ρ.Equiv (R.prod R)) (hm : Models R) : DoubledModels ρ := by
  rcases hm with h | h | h
  · exact Or.inl (double_coordinates ρ R _ d h)
  · exact Or.inr (Or.inl (double_coordinates ρ R _ d h))
  · exact Or.inr (Or.inr (double_coordinates ρ R _ d h))


/-- A faithful ambient action inside the native permutation tensor normalizer,
with the original normal component marked in the first factor. -/
@[expose] def PermutationTensorEmbedding (ρ : Representation (ZMod 2) D W)
    (H : Subgroup D) {n : ℕ} {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin n)) U) : Prop :=
  ∃ e : H ≃* alternatingGroup (Fin n),
    ∃ j : D →* (Equiv.Perm (Fin n) × Equiv.Perm (Fin 3)),
      ∃ t : W ≃ₗ[ZMod 2] (U ⊗[ZMod 2] BinaryPermutation.core (Fin 3)),
        Function.Injective j ∧
        (∀ a w, t (ρ a w) = BinaryPermutation.ThreeTensor.action σ (j a) (t w)) ∧
        ∀ h : H, j h = ((e h).val,1)

/-- The natural SL₂(4) double or an actual whole-group embedding in one
of the two permutation tensor normalizers. Surjectivity is not asserted. -/
@[expose] def AmbientModels (ρ : Representation (ZMod 2) D W) (H : Subgroup D) : Prop :=
  let N := SL2.BinarySmall.natural (K := OrthogonalFourMinus.FiniteModel.Field 1)
  Quasiequivalent (ρ.comp H.subtype) (N.prod N) ∨
    PermutationTensorEmbedding ρ H (BinaryPermutation.coreRepresentation (Fin 5)) ∨
    PermutationTensorEmbedding ρ H (BinaryPermutation.naturalRepresentation (Fin 6))

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem five_embedding (ρ : Representation (ZMod 2) D W)
    (hfρ : Function.Injective ρ) (H : Subgroup D) [H.Normal]
    (hm : Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 5)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)))) :
    PermutationTensorEmbedding ρ H (BinaryPermutation.coreRepresentation (Fin 5)) := by
  obtain ⟨e,f,hf⟩ := hm
  let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  have hc (a : alternatingGroup (Fin 5)) (w : BinaryPermutation.natural (Fin 5)) :
      c.symm (BinaryPermutation.alternatingNaturalRepresentation (Fin 5) a w) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) a (c.symm w) := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact (BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide)
      a (c.symm w)).trans (by rw [c.apply_symm_apply]; rfl) |>.symm
  let f' := f.trans (c.symm.prodCongr c.symm)
  have hf' (h : H) (w : W) : f' (ρ h w) =
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (e h) (f' w).1,
       BinaryPermutation.alternatingCoreRepresentation (Fin 5) (e h) (f' w).2) := by
    have hh := hf h w
    change f (ρ h w) =
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (e h) (f w).1,
       BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (e h) (f w).2) at hh
    change (c.symm (f (ρ h w)).1,c.symm (f (ρ h w)).2) = _
    rw [hh,hc,hc]
    rfl
  obtain ⟨j,t,hj,ht,hmark⟩ :=
    BinaryPermutation.FiveTensorNormalizer.exists_tensor_embedding_of_double ρ hfρ H e f' hf'
  exact ⟨e,j,t,hj,ht,hmark⟩

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem six_embedding (ρ : Representation (ZMod 2) D W)
    (hfρ : Function.Injective ρ) (H : Subgroup D) [H.Normal]
    (hm : Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 6)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))) :
    PermutationTensorEmbedding ρ H (BinaryPermutation.naturalRepresentation (Fin 6)) := by
  obtain ⟨e,f,hf⟩ := hm
  obtain ⟨j,t,hj,ht,hmark⟩ :=
    BinaryPermutation.SixDoubleNormalizer.exists_tensor_embedding_of_double ρ hfρ H e f hf
  exact ⟨e,j,t,hj,ht,hmark⟩

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem ambient_models (ρ : Representation (ZMod 2) D W)
    (hfρ : Function.Injective ρ) (H : Subgroup D) [H.Normal]
    (hm : DoubledModels (ρ.comp H.subtype)) : AmbientModels ρ H := by
  rcases hm with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (five_embedding ρ hfρ H h))
  · exact Or.inr (Or.inr (six_embedding ρ hfρ H h))

/-- The original selected constituent, with actual models in the marked
branch and literal exchanged-constituent geometry in the other branch. -/
@[expose] def ConstituentReduction (ρ : Representation (ZMod 2) D W)
    (B : LinearMap.BilinForm (ZMod 2) W) (v : W) (E : Submodule (ZMod 2) W)
    (X : Subgroup D) [IsElementaryAbelian 2 X] : Prop :=
  ∃ C : Subgroup D, IsComponent D C ∧ ⁅C,X⁆ ≠ ⊥ ∧
    ChapterG.Section10.ComponentOrthogonalData ρ B C ∧
    ∃ I : Submodule (ZMod 2) W, ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I,
      (v ∈ I ∧ C.Normal ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) W = 8 ∧
        Nat.card X = 8 ∧
        Models (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation ∧
        DoubledModels (ρ.comp (componentOrbit C ⊤).subtype) ∧
        AmbientModels ρ (componentOrbit C ⊤)) ∨
      (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry ρ B v E X I)

end FixedLineActions

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
universe u
section Marked
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
  (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives classification hne hZ hlarge hgP hgH hyp hC hm hI hv


/-- Actual action models for the original constituent through the marked point.
The self-dual condition excludes the four-dimensional A₇ action. -/
theorem source_large_fixed_line_marked_actions
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    C.Normal ∧ finrank (ZMod 2) I = 4 ∧
      finrank (ZMod 2) (Additive F.Uhat) = 8 ∧ Nat.card (F.terminalDot (F.X g)) = 8 ∧
      FixedLineActions.Models R.toRepresentation := by
  let := chosen.elementary
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let R := invariantSubspace F.terminalRepresentation H I hI.choose
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hns
  let : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction _ hi H
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have hdata := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hns hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  have hHC := (source_large_fixed_line_component_normal d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).1
  obtain ⟨hCn,hmodels⟩ := source_large_fixed_line_component_models d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  obtain ⟨hI4,hV8,hX8⟩ := source_large_fixed_line_marked_degree d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  refine ⟨hCn,hI4,hV8,hX8,?_⟩
  let eH : H ≃* C := MulEquiv.subgroupCongr hHC
  rcases hmodels with ⟨e5⟩ | ⟨e6⟩ | ⟨e7⟩
  · exact FixedLineActions.five_models R.toRepresentation hdata.2.1 (eH.trans e5.some)
  · exact FixedLineActions.six_models R.toRepresentation hI4 (eH.trans e6.some)
  · exact (FixedLineActions.Seven.no_selfDual R.toRepresentation hdata.2.1
      (eH.trans e7.some) hI4 hdata.2.2.1).elim

/-- The whole original module has actual double coordinates for its normal
component orbit, using a single actor identification on both copies. -/
theorem source_large_fixed_line_double_actions
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineActions.DoubledModels
      (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype) := by
  let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
  have hmR := (source_large_fixed_line_marked_actions d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).2.2.2.2
  obtain ⟨a⟩ := (source_large_marked_double d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2
  exact FixedLineActions.doubled_models _ R.toRepresentation a hmR

/-- Extend the original marked component coordinates to the actual ambient
terminal action in the permutation rows. The natural SL₂(4) double remains
explicit for its semilinear recognition. -/
theorem source_large_fixed_line_ambient_actions
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineActions.AmbientModels F.terminalRepresentation (componentOrbit C ⊤) := by
  let : (componentOrbit C ⊤).Normal := componentOrbit_top_normal C
  exact FixedLineActions.ambient_models _ hyp.faithful _
    (source_large_fixed_line_double_actions d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn)

end Marked

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
  (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))


include d earlier hq chosen structural alternatives classification hne hZ hlarge hgP hgH hyp

/-- Select the original component and constituent from the ambient source
hypotheses. Its marked branch has concrete models on the full component
restriction; the other branch retains its actual exchanged geometry. -/
theorem source_large_fixed_line_constituent_reduction
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineActions.ConstituentReduction F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  let := chosen.elementary
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hF := hyp.fitting_centralizer_ne_bot_of_not_solvable (source_terminal_cover F d chosen) hns
  obtain ⟨C,hC,hm,hsel,horth⟩ := hyp.exists_moved_component_orthogonal_selection hns hF
  obtain ⟨_,_,I,hI,_⟩ := hsel
  refine ⟨C,hC,hm,horth,I,hI,?_⟩
  by_cases hv : v ∈ I
  · left
    obtain ⟨hCn,hI4,hV8,hX8,hmodel⟩ := source_large_fixed_line_marked_actions d earlier hq chosen
      structural alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn
    exact ⟨hv,hCn,hI4,hV8,hX8,hmodel,source_large_fixed_line_double_actions d earlier hq chosen
      structural alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn,
      source_large_fixed_line_ambient_actions d earlier hq chosen structural alternatives
        classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn⟩
  · right
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
      structural alternatives F hne g hgP hgH
    have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
    exact ⟨hv,hyp.exchanged_constituent_geometry hns hC hm P
      ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

