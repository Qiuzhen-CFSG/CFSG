module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.Kernel
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.QuotientNumericalSource
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.SL2NaturalOffenders
public import GorensteinWalter.SL2ProjectiveCover

/-!
# The common offender lies in the residual in the larger linear rows

For a single natural SL₂ component, the faithful normalizer theorem puts
any offender inside that component. Applied to the actual source section,
the fitting-layer identity puts every best offender in the two-residual.
For a marked pair over a field of order at least four, the offender group
is a product of perfect SL₂ groups and hence lies in the residual directly.
The original sharp chief offender is best by the proved ratio lower bound.

These literal subgroup containments support the common-actor comparison in
Aschbacher–Smith3.1.9(5), printed p.578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
private theorem linear_natural_offender_le_layer
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D) [L.Normal]
    (F : BinaryField) (hF : 2 < Nat.card F.Carrier)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2))
    (hf : Function.Injective ρ) {A : Subgroup D} (hA : IsOffender ρ A) : A ≤ L := by
  let τ : Representation (ZMod 2) D (Fin 2 → F.Carrier) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  have ht : ∀ g v, e.linearEquiv (ρ g v) = τ g (e.linearEquiv v) := by
    intro g v
    change e.linearEquiv (ρ g v) = e.linearEquiv (ρ g (e.linearEquiv.symm (e.linearEquiv v)))
    rw [e.linearEquiv.symm_apply_apply]
  have hfτ : Function.Injective τ := e.linearEquiv.conjRingEquiv.injective.comp hf
  have hnat : ∀ (g : L) v, τ (g : D) v = Matrix.mulVec (e.groupEquiv g).val v := by
    intro g v
    obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
    rw [← ht]
    exact e.intertwines g w
  have hAτ : IsOffender τ A := by
    have hh := hA.map_equivariant ρ τ (MonoidHom.id D) Function.injective_id e.linearEquiv ht
    simpa only [Subgroup.map_id] using hh
  obtain ⟨P,hP⟩ := SL2NaturalOffenders.exists_sylow hF L e.groupEquiv τ hfτ hnat hAτ
  exact hP ▸ Subgroup.map_subtype_le _

theorem source_quasisimple_linear_offender_le_residual
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (T : Sylow 2 D)
    (hp : IsMinimalParabolicOver T ⊤) (hff : IsFFModule ρ) (hc : pCore 2 D = ⊥)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField) (hF : 2 < Nat.card F.Carrier)
    (hn : IsLinearNatural (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype) F 2)
    {A : Subgroup D} (hA : IsBestOffender ρ A) : A ≤ pResidual 2 D := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  have hAY : A ≤ Y := hA.le_offenderSubgroup ρ
  let B := A.subgroupOf Y
  have hB : IsOffender c.sectionData.action B :=
    ((hA.isOffender ρ).subgroupOf ρ hAY).on_subquotient
      (ρ.comp Y.subtype) c.sectionData.space c.sectionData.central
  obtain ⟨e⟩ := hn
  have hBL := linear_natural_offender_le_layer c.sectionData.action _ F hF e
    (source_offender_quasisimple_irreducible ρ T hp hff hc hqs c).2.1 hB
  have hm := Subgroup.map_mono (f := Y.subtype) hBL
  rw [map_subgroupOf_eq_of_le hAY,
    (source_quasisimple_fitting_eq_residual T hp Y (offender_generation T hp ρ hff hc).2 hqs).1] at hm
  exact hm

theorem source_pair_linear_offender_le_residual
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (c : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (hF : 3 < Nat.card F.Carrier)
    (e : c.MarkedProduct (linearNatural F 2))
    {A : Subgroup D} (hA : IsBestOffender ρ A) : A ≤ pResidual 2 D := by
  let Y := offenderSubgroup ρ
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hF
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F.Carrier ×
      Matrix.SpecialLinearGroup (Fin 2) F.Carrier) := ⟨by
    rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod]
    simp only [← commutator_def, Group.IsPerfect.commutator_eq_top]⟩
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective (f := e.action.groupEquiv.symm.toMonoidHom) e.action.groupEquiv.symm.surjective
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact (hA.le_offenderSubgroup ρ).trans (le_of_isPerfect_of_solvable_quotient Y _)

universe u
theorem minimalParabolic_sharp_image_isBestOffender
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [Representation.IsIrreducible ρ]
    (hD : IsSQTK KnownSimple.IsKnownSimple D) (T : Sylow 2 D)
    (hp : IsMinimalParabolicOver T ⊤)
    {A : Subgroup (actionImage ρ)}
    (hA : IsOffender (Representation.BinaryOffender.imageRepresentation ρ) A)
    (heq : rank A = fixedCodim (Representation.BinaryOffender.imageRepresentation ρ) A) :
    IsBestOffender (Representation.BinaryOffender.imageRepresentation ρ) A := by
  have hn : ¬ IsStrongFFModule (Representation.BinaryOffender.imageRepresentation ρ) := by
    intro hh
    exact not_lt_of_ge (minimalParabolic_irreducible_image_quadraticRatio_ge_one hD T hp ρ)
      ((isStrongFFModule_iff_quadraticRatio_lt_one _).mp hh)
  exact (isBestOffender_iff_of_not_strong _ hn A).mpr ⟨hA.1,heq.symm⟩
end CFSG.Quasithin.ChapterB
