module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NormalSupplementModels
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Natural
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Hexacode
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.HexacodeEven
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels
public import Theory.Representation.BinaryOffender.QuasisimpleNormalizer

/-!
# Minimal-parabolic obstructions through the original quotient action

A faithful quotient action of a normal subgroup identifies that quotient
with the subgroup's image in the whole action image. Nonsolvability makes
minimal parabolicity descend to this image. Its normal natural SL3, natural
A6 or even hexacode restriction then contradicts the checked normalizer
and two-parabolic obstructions. The ambient action need not be faithful.

The original quotient projection and every operator are retained. The
Chapter 12 applications are in LocalConfigurationNaturalHStarSourceActionRows.
Source: Aschbacher--Smith, 12.2.7, printed pp.797--798, comparing E.2.2
with the chosen-module rows of 12.2.2; B.6.9 and K.1.1--3.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.QuasisimpleNormalizer
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G Q W : Type*} [Group G] [Finite G] [Group Q]
  [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem image_coordinates
    (ρ : Representation (ZMod 2) G W) (K : Subgroup G)
    (σ : Representation (ZMod 2) Q W) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) :
    ∃ e : K.map ρ.asGroupHom.rangeRestrict ≃* Q,
      ∀ k : K, e ((ρ.asGroupHom.rangeRestrict.subgroupMap K) k) = q k := by
  let f := ρ.asGroupHom.rangeRestrict.subgroupMap K
  have hk : f.ker = q.ker := by
    ext k
    change f k = 1 ↔ q k = 1
    constructor
    · intro h
      apply hf
      rw [map_one, ← he]
      exact congrArg (fun z : K.map ρ.asGroupHom.rangeRestrict => z.val.val.val) h
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      change ρ k = 1
      rw [he, h, map_one]
  let e : K.map ρ.asGroupHom.rangeRestrict ≃* Q :=
    (QuotientGroup.quotientKerEquivOfSurjective f
      (ρ.asGroupHom.rangeRestrict.subgroupMap_surjective K)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  refine ⟨e, ?_⟩
  intro k
  let E := QuotientGroup.quotientKerEquivOfSurjective f
    (ρ.asGroupHom.rangeRestrict.subgroupMap_surjective K)
  have hE : E (QuotientGroup.mk' f.ker k) = f k := rfl
  change (QuotientGroup.quotientKerEquivOfSurjective q hq)
    ((QuotientGroup.quotientMulEquivOfEq hk) (E.symm (f k))) = q k
  rw [← hE, E.symm_apply_apply]
  rfl

omit [Finite G] in
private theorem image_action_equiv
    (ρ : Representation (ZMod 2) G W) (K : Subgroup G)
    (σ : Representation (ZMod 2) Q W) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) :
    Nonempty (ActionEquiv
      ((linearAction ρ.asGroupHom.range).comp (K.map ρ.asGroupHom.rangeRestrict).subtype) σ) := by
  obtain ⟨e,heq⟩ := image_coordinates ρ K σ hf q hq he
  refine ⟨⟨e, LinearEquiv.refl _ _, ?_⟩⟩
  intro k w
  obtain ⟨l,rfl⟩ := ρ.asGroupHom.rangeRestrict.subgroupMap_surjective K k
  change ρ l w = σ (e ((ρ.asGroupHom.rangeRestrict.subgroupMap K) l)) w
  rw [heq,he]

private theorem image_minimal
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) G W) (K : Subgroup G)
    (σ : Representation (ZMod 2) Q W) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) (hs : ¬ Group.IsSolvable Q) :
    IsMinimalParabolicOver (T.mapSurjective ρ.asGroupHom.rangeRestrict_surjective) ⊤ := by
  obtain ⟨e,_⟩ := image_coordinates ρ K σ hf q hq he
  apply minimalParabolic_surjective_of_not_solvable T hP
    ρ.asGroupHom.rangeRestrict ρ.asGroupHom.rangeRestrict_surjective
  intro hh
  let := hh
  exact hs (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- Natural coordinates on a quotient of a normal Sylow supplement exclude
minimal parabolicity, even when the ambient action has a nontrivial kernel. -/
theorem not_minimalParabolic_of_quotient_natural_three
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (ρ : Representation (ZMod 2) G W)
    (σ : Representation (ZMod 2) Q W) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) (hs : ¬ Group.IsSolvable Q)
    (e : ActionEquiv σ (specialLinearNatural (k := ZMod 2) 3)) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  intro hP
  let : Finite ρ.asGroupHom.range := Finite.of_surjective _ ρ.asGroupHom.rangeRestrict_surjective
  let a := ρ.asGroupHom.rangeRestrict
  let S := T.mapSurjective ρ.asGroupHom.rangeRestrict_surjective
  let J := K.map a
  let : J.Normal := (inferInstance : K.Normal).map a ρ.asGroupHom.rangeRestrict_surjective
  have hg : J ⊔ (S : Subgroup _) = ⊤ := by
    change K.map a ⊔ (T : Subgroup G).map a = _
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective _ ρ.asGroupHom.rangeRestrict_surjective]
  obtain ⟨c⟩ := image_action_equiv ρ K σ hf q hq he
  exact not_minimalParabolic_of_natural_three S J hg (linearAction ρ.asGroupHom.range)
    BinaryField.two ⟨c.trans e⟩ (image_minimal T hP ρ K σ hf q hq he hs)

/-- The normal natural A₆ quotient obstruction retains its original action. -/
theorem not_minimalParabolic_of_quotient_natural_six
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (ρ : Representation (ZMod 2) G W)
    (σ : Representation (ZMod 2) Q W) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) (hs : ¬ Group.IsSolvable Q)
    (e : ActionEquiv σ (alternatingNatural 6)) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  intro hP
  let : Finite ρ.asGroupHom.range := Finite.of_surjective _ ρ.asGroupHom.rangeRestrict_surjective
  let a := ρ.asGroupHom.rangeRestrict
  let J := K.map a
  let : J.Normal := (inferInstance : K.Normal).map a ρ.asGroupHom.rangeRestrict_surjective
  obtain ⟨c⟩ := image_action_equiv ρ K σ hf q hq he
  exact not_minimalParabolic_of_natural_alternatingSix _ J (linearAction ρ.asGroupHom.range)
    (c.trans e) (image_minimal T hP ρ K σ hf q hq he hs)

/-- The faithful irreducible six-dimensional even-cover quotient also excludes
minimal parabolicity; recognition constructs the actual hexacode coordinates. -/
theorem not_minimalParabolic_of_quotient_hexacode [Module.Finite (ZMod 2) W]
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (ρ : Representation (ZMod 2) G W)
    (σ : Representation (ZMod 2) Q W) (hf : Function.Injective σ)
    (q : K →* Q) (hq : Function.Surjective q)
    (he : ∀ k : K, ρ k = σ (q k)) (hs : ¬ Group.IsSolvable Q)
    (e : Q ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hi : IsIrreducible σ) (hd : Module.finrank (ZMod 2) W = 6) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  intro hP
  let : Finite ρ.asGroupHom.range := Finite.of_surjective _ ρ.asGroupHom.rangeRestrict_surjective
  let a := ρ.asGroupHom.rangeRestrict
  let J := K.map a
  let : J.Normal := (inferInstance : K.Normal).map a ρ.asGroupHom.rangeRestrict_surjective
  let τ := σ.comp e.symm.toMonoidHom
  have hiτ : IsIrreducible τ :=
    (irreducible_comp_surjective_iff _ e.symm.surjective σ).mpr hi
  obtain ⟨c⟩ := ChapterK.Alternating.EvenRecognition.exists_actionEquiv τ
    (hf.comp e.symm.injective) hiτ hd
  let b : ActionEquiv σ τ := ⟨e,LinearEquiv.refl _ _,fun g v => by
    change σ g v = σ (e.symm (e g)) v
    rw [e.symm_apply_apply]⟩
  obtain ⟨d⟩ := image_action_equiv ρ K σ hf q hq he
  exact not_minimalParabolic_of_even_hexacode _ J (linearAction ρ.asGroupHom.range)
    ((d.trans b).trans c) (image_minimal T hP ρ K σ hf q hq he hs)

end CFSG.Quasithin.ChapterB
