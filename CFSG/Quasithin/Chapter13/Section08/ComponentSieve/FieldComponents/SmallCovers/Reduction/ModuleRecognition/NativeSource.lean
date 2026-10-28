module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Hexacode
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders
public import Theory.GroupTheory.GeneralizedFitting.NormalComponentCentralizer

/-!
# Native recognition for the cubic six-cover sections

The genuine normal six-cover and its centralizer bound identify the
component with the generalized Fitting subgroup of every intermediate
overgroup. The proved K.1 degree theorem forces six binary dimensions
under the small quadratic-ratio bound. Its actual hexacode coordinates
and permitted ambient extension give the faithful marked actor, while
the checked offender calculation gives ratio one.

This discharges both universal irreducible inputs used by the six-cover
reduction, without assuming a module catalogue or a selected source
constituent. The original field-sieve owner qt-d-138-fields-source retains
selection and the terminal V_H/U_H argument; qt-d-1381-source supplies
the earlier local setup.
Source: Aschbacher–Smith, K.1.3, p.453; B.4.2(8), B.4.5, pp.86–87;
application in 13.8.21(2), p.956. The imported concrete hexacode recognition
retains the existing ATLAS attribution.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.NativeSource
universe u v
variable {D : Type u} [Group D] [Finite D] {κ : GroupClass.{u}}

private noncomputable def centralEquiv {E : Type*} [Group E] (e : E ≃* HexEvenAutomorphisms) :
    (E ⧸ center E) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)).trans
    Hexacode.even_quotient_center_equiv

private theorem overgroup_fitting (L : Subgroup D) [L.Normal]
    (e : L ≃* HexEvenAutomorphisms) (hcent : centralizer (L : Set D) ≤ L)
    (J : Subgroup D) (hLJ : L ≤ J) : generalizedFitting J = L.subgroupOf J := by
  let C := L.subgroupOf J
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv ((subgroupOfEquivOfLe hLJ).trans e).symm
  have hc : centralizer (C : Set J) ≤ C := by
    intro x hx
    apply hcent
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx (⟨l,hLJ hl⟩ : J) hl)
  rw [generalizedFitting_eq_normal_component_sup_centralizer C]
  exact sup_eq_left.mpr ((map_subtype_le _).trans hc)

omit [Finite D] in
private theorem model_of_action {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D)
    (a : ChapterK.Alternating.HexacodeAction ρ L) : Nonempty (HexacodeModel L ρ) := by
  rcases a.extension with ht | hm
  · subst L
    let e := ChapterK.Alternating.wholeAction rfl a.restricted
    refine ⟨{
      actor := hexSign.ker.subtype.comp e.groupEquiv.toMonoidHom
      faithful := hexSign.ker.subtype_injective.comp e.groupEquiv.injective
      component_image := ?_
      coordinates := e.linearEquiv
      intertwines := e.intertwines }⟩
    rw [← map_map, map_top_of_surjective _ e.groupEquiv.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  · obtain ⟨m⟩ := hm
    let e := ChapterK.Alternating.wholeAction rfl m.action
    exact ⟨{
      actor := e.groupEquiv.toMonoidHom
      faithful := e.groupEquiv.injective
      component_image := ChapterK.Alternating.HexacodeOffenders.marked_even_map m
      coordinates := e.linearEquiv
      intertwines := e.intertwines }⟩

private theorem recognized {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D) [L.Normal]
    (hD : IsSQTK κ D)
    (e : L ≃* HexEvenAutomorphisms) (hfit : generalizedFitting D = L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    (hq : quadraticRatio ρ ≤ 2) :
    Nonempty (HexacodeModel L ρ) ∧ quadraticRatio ρ = 1 := by
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  have hyp : ChapterK.Alternating.Input ρ κ L := {
    sqtk := hD
    fitting := hfit.symm
    quasisimple := IsQuasisimple.of_mulEquiv e.symm
    faithful := hf
    irreducible := hi
    cubic_bound := (cubicRatio_le_quadraticRatio ρ).trans hq
    quotient := Or.inl ⟨centralEquiv e⟩ }
  obtain ⟨a⟩ := ChapterK.Alternating.hexacodeAction_of_dimension ρ hyp e
    (ChapterK.Alternating.tripleSixDegree ρ κ L hyp e)
  exact ⟨model_of_action ρ L a,(ChapterK.Alternating.HexacodeOffenders.source a).2.2⟩

/-- The exact universal B.4 contracts for all intermediate overgroups of the cover. -/
theorem irreducibleInputs (L : Subgroup D) [L.Normal]
    (hD : IsSQTK κ D)
    (e : L ≃* HexEvenAutomorphisms) (hcent : centralizer (L : Set D) ≤ L) :
    IrreducibleInputs.{u,v} L := by
  constructor
  · intro J hLJ W _ _ _ σ hf hi hq
    exact (recognized σ (L.subgroupOf J) (hD.subgroup J)
      ((subgroupOfEquivOfLe hLJ).trans e) (overgroup_fitting L e hcent J hLJ) hf hi hq).1
  · intro J hLJ W _ _ _ σ hf hi hff
    exact (recognized σ (L.subgroupOf J) (hD.subgroup J)
      ((subgroupOfEquivOfLe hLJ).trans e) (overgroup_fitting L e hcent J hLJ) hf hi
      (((isFFModule_iff_quadraticRatio_le_one σ).mp hff).trans (by norm_num))).2
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.NativeSource
