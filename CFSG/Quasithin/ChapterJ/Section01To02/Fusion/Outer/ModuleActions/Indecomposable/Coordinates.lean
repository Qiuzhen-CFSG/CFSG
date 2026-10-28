module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Indecomposable.Cohomology
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FieldDescent

/-!
# Frobenius coordinates for the marked natural head in J.2.5

The given marking identifies the image of A₅ with the actual natural SL₂(4)
image. Normality of A₅ puts every S₅ actor in its binary linear normalizer,
and faithfulness keeps every odd actor outside SL₂(4). The normalizer theorem
then makes an odd involution Frobenius-semilinear for the original F₄ scalars.
This supplies the explicit coordinate witness for the natural dual H¹ bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, J.2.2(3) and
J.2.5, printed pp.432, 434 (PDF pp.443, 445 of `refs/quasithin.pdf`);
the semilinear normalizer calculation is in 6.2.5, printed pp.680–681.
-/

public section

open Representation Representation.SL2FourNatural
open Representation.SL2FourNatural.SemilinearNormalizer
noncomputable section
namespace CFSG.Quasithin.ChapterJ.L2FourAction

/-- An odd involution in the given natural S₅ action is an F₄-linear map after
coordinate Frobenius, with the original marking and vector coordinates. -/
theorem exists_outer_frobenius (r : L2FourAction) (t : S5) (ht : t ∉ alternatingGroup (Fin 5))
    (ht2 : t * t = 1) :
    ∃ A : V ≃ₗ[F] V, ∀ v, r.action t v = A (frobeniusLinear v) := by
  let φ : S5 →* BinaryGL :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
      r.action.asGroupHom
  have hφ (s : S5) (v : V) : φ s v = r.action s v := rfl
  have hr (g : SL) : φ (r.marking g) = SL2FourNatural.action g := by
    apply LinearEquiv.ext
    exact r.restriction g
  have him : (alternatingGroup (Fin 5)).map φ = SL2FourNatural.action.range := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨r.marking.symm ⟨a, ha⟩, ?_⟩
      rw [← hr, r.marking.apply_symm_apply]
    · rintro ⟨g, rfl⟩
      exact ⟨r.marking g, (r.marking g).property, hr g⟩
  have hn : φ t ∈ normalizer := by
    change φ t ∈ Subgroup.normalizer (SL2FourNatural.action.range : Set BinaryGL)
    rw [← him]
    apply Subgroup.le_normalizer_map φ
    exact ⟨t, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩
  have hnot : φ t ∉ SL2FourNatural.action.range := by
    rintro ⟨g, hg⟩
    apply ht
    have he : t = r.marking g := by
      apply r.injective
      apply LinearMap.ext
      intro v
      rw [← hφ, ← hφ, hr, hg]
    rw [he]
    exact (r.marking g).property
  have h2 : φ t ^ 2 = 1 := by rw [pow_two, ← map_mul, ht2, map_one]
  let g := normalizerEquiv.symm ⟨φ t, hn⟩
  have hc : g.right = fieldFrobenius := normalizer_involution_coefficients _ hn h2 hnot
  have he : natural g = φ t :=
    congrArg Subtype.val (normalizerEquiv.apply_symm_apply ⟨φ t, hn⟩)
  refine ⟨glEquiv g.left, ?_⟩
  intro v
  rw [← hφ, ← he, natural_apply, hc]
  rfl

/-- The contragredient natural S₅ cohomology has binary dimension at most one.
The outer actor's Frobenius coordinates are proved from the marked action. -/
theorem finrank_dual_H1_le_one (r : L2FourAction)
    (t : S5) (ht : t ∉ alternatingGroup (Fin 5)) (ht2 : t * t = 1) :
    Module.finrank (ZMod 2) (OneCohomology.H1 r.action.dual) ≤ 1 := by
  obtain ⟨A, hA⟩ := r.exists_outer_frobenius t ht ht2
  exact r.finrank_dual_H1_le_one_of_frobenius t ht ht2 A hA

end CFSG.Quasithin.ChapterJ.L2FourAction
