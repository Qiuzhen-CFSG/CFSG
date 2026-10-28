module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.SmallModuleRecognition.Inputs
public import Theory.Representation.EndFieldDegree
public import Theory.Representation.Triality.InnerDisplacement.CoverReduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Reduction of small binary Rudvalis recognition to three calculations

A faithful irreducible binary action kills a central two-group. After the
multiplier upper bound removes the center, transport the action to the actual
Ru carrier. Its Schur-field representation is absolutely irreducible. Absolute
degree 28 and binary degree at most 36 force the Schur field to have degree
one, so the original binary module is absolutely irreducible of degree 28.
Finally a nonzero generator intertwiner extends to the generated group;
irreducibility and equal dimensions make it an equivalence.

The three input calculations remain explicit. This is not the unconditional
small-module classification. Its final assembly is retained in this module.
Sources: Aschbacher--Smith, printed pp.451, 457; Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1 (Ru); Hiss--Malle,
corrected Table 2, p.102.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
open Theory.GroupTheory Subgroup Representation SmallModuleRecognitionInputs
open scoped MonoidAlgebra
universe u v

/-- Scalar descent in the exact binary degree window, including the proof of
absolute irreducibility rather than assuming it of the source module. -/
theorem binary_window_of_absolute_degree_window
    (hdegree : AbsoluteDegreeWindow.{v}) [IsQuasisimple Rudvalis.Model]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V ≤ 36) :
    Module.finrank (ZMod 2) V = 28 ∧ σ.IsAbsolutelyIrreducible := by
  let := hi
  let K := Module.End (ZMod 2)[Rudvalis.Model] σ.asModule
  let : Finite σ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional K σ.asModule := Module.Finite.of_finite
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have h28 : Module.finrank K σ.asModule = 28 :=
    hdegree inferInstance K σ.asModule σ.endFieldRep
      ((endFieldRep_injective_iff σ).mpr hf) (endFieldRep_isAbsolutelyIrreducible σ)
      ((endField_finrank_le σ).trans hd)
  have hdim := finrank_eq_endField_mul σ
  change Module.finrank (ZMod 2) V =
    Module.finrank (ZMod 2) K * Module.finrank K σ.asModule at hdim
  rw [h28] at hdim
  have hpos : 0 < Module.finrank (ZMod 2) K := Module.finrank_pos
  have hK : Module.finrank (ZMod 2) K = 1 := by omega
  refine ⟨by omega, (isAbsolutelyIrreducible_iff_surjective σ).mpr ?_⟩
  apply (algebraMap_surj_iff_surj σ).mp
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hK).2

/-- The two ATLAS generators suffice for the full action identity. -/
theorem intertwines_of_generator_equations
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) Rudvalis.Model V)
    (e : Rudvalis.Model ≃* standardGroup)
    (ha : (e Rudvalis.a).val = generatorA) (hb : (e Rudvalis.b).val = generatorB)
    (T : V →ₗ[ZMod 2] Space)
    (hTa : ∀ v, T (σ Rudvalis.a v) = generatorA.val (T v))
    (hTb : ∀ v, T (σ Rudvalis.b v) = generatorB.val (T v)) :
    ∀ g v, T (σ g v) = standardRepresentation (e g) (T v) := by
  let τ := standardRepresentation.comp e.toMonoidHom
  let H : Subgroup Rudvalis.Model :=
    { carrier := {g | ∀ v, T (σ g v) = τ g (T v)}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro g h hg hh v
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hg, hh]
      inv_mem' := by
        intro g hg v
        have h := congrArg (τ g⁻¹) (hg (σ g⁻¹ v))
        simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          mul_inv_cancel, map_one, Module.End.one_apply] using h.symm }
  have hH : H = ⊤ := Rudvalis.eq_top_of_a_mem_of_b_mem H
    (by
      intro v
      change T (σ Rudvalis.a v) = (e Rudvalis.a).val.val (T v)
      rw [ha]
      exact hTa v)
    (by
      intro v
      change T (σ Rudvalis.b v) = (e Rudvalis.b).val.val (T v)
      rw [hb]
      exact hTb v)
  intro g
  exact (show g ∈ H from hH ▸ mem_top g)

/-- A nonzero degree-28 generator intertwiner is already a module marking.
No irreducibility assumption about the fixed matrix module is needed. -/
theorem marking_of_degree28_generator_intertwining
    (hinter : Degree28GeneratorIntertwining.{v}) [IsQuasisimple Rudvalis.Model]
    (e : Rudvalis.Model ≃* standardGroup)
    (ha : (e Rudvalis.a).val = generatorA) (hb : (e Rudvalis.b).val = generatorB)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective σ) (hi : σ.IsAbsolutelyIrreducible)
    (hd : Module.finrank (ZMod 2) V = 28) :
    ∃ E : V ≃ₗ[ZMod 2] Space,
      ∀ g v, E (σ g v) = standardRepresentation (e g) (E v) := by
  let := hi
  let : σ.IsIrreducible :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible σ
  obtain ⟨T, hT, hTa, hTb⟩ := hinter e ha hb inferInstance V σ hf hi hd
  have hcomm := intertwines_of_generator_equations σ e ha hb T hTa hTb
  let f : σ.IntertwiningMap (standardRepresentation.comp e.toMonoidHom) :=
    ⟨T, fun g => LinearMap.ext (hcomm g)⟩
  have hfne : f ≠ 0 := by
    intro he
    apply hT
    exact congrArg IntertwiningMap.toLinearMap he
  have hinj : Function.Injective T := (IsIrreducible.injective_or_eq_zero f).resolve_right hfne
  have hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) Space :=
    hd.trans finrank_space.symm
  let E := LinearEquiv.ofBijective T
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  exact ⟨E, hcomm⟩

/-- Application to every covering group and the literal representation in the
published recognition contract. All three unproved inputs remain visible. -/
theorem smallModuleRecognition_of_calculations
    (hmodel : StandardComparison) (hcenter : TwoPrimaryCoverCenters.{u})
    (hdegree : AbsoluteDegreeWindow.{v})
    (hinter : Degree28GeneratorIntertwining.{v}) : SmallModuleRecognition.{u,v} := by
  intro L V _ _ _ _ _ _ σ hf hi he hd
  let := hi
  obtain ⟨q⟩ := he
  have hc : center L = ⊥ :=
    Triality.InnerDisplacement.center_eq_bot_of_twoGroup σ hf (hcenter ⟨q⟩)
  let c : L ≃* Rudvalis.Model :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans q
  let : IsQuasisimple Rudvalis.Model := IsQuasisimple.of_mulEquiv c
  let τ : Representation (ZMod 2) Rudvalis.Model V := σ.comp c.symm.toMonoidHom
  have hτf : Function.Injective τ := hf.comp c.symm.injective
  have hτi : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff c.symm.toMonoidHom c.symm.surjective σ).mpr hi
  obtain ⟨h28, habs⟩ := binary_window_of_absolute_degree_window hdegree τ hτf hτi hd
  obtain ⟨e, ha, hb⟩ := hmodel
  obtain ⟨E, hE⟩ := marking_of_degree28_generator_intertwining hinter e ha hb τ hτf habs h28
  refine ⟨c.trans e, E, ?_⟩
  intro l v
  have h := hE (c l) v
  change E (σ (c.symm (c l)) v) = standardRepresentation (e (c l)) (E v) at h
  simpa only [MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using h

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
