module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated.PlaneGeometry

/-!
# Exclusion of the repeated-natural alternative in 15.3.24

The actual plane marking and the genuine earlier local conclusions suffice
to exclude every repeated-natural commutator module. Cubic elements of the
plane parabolic give both the nontrivial projected-centralizer two-residual
and the vanishing of its natural fixed space. Equivariant coordinates and
the checked extension splitting transport these calculations to U_L and W_L.

Projection identifies O²(C_{Y₊}(Z_L)) with O²(C_{Y₊}(Z)); the earlier
intersection factorization puts it in O²(C_{Y₊}(V)). Its nontriviality
forces the extraspecial case of 15.3.7. The actual E₉ quotient of Y₊ then
gives Y₊ < Y and the second choice of Hypothesis 15.3.10. Now V₁ lies in
C_{W_L}(Y₊) = C_{W_L}(L), and the exact plane-normalizer bound of
15.3.11(3) contradicts the outside component.

`Preparation.Earlier`, elementarity of W_L, the bound R ≤ C_G(V), the
centralizer and intersection equalities, and the complete 15.3.7 alternatives are
explicit genuine earlier-theorem inputs. The plane marking is a preparation
output whose construction remains with its owner. No residual nontriviality,
fixed-space equality, branch choice, or terminal containment is assumed here.
The argument does not require the multiplicity bounds 0 < r ≤ 3, so it
applies in particular to the repeated branch of `ModuleAlternatives`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.24,
printed p.1129 (PDF p.1146); 15.3.7, 15.3.10 and 15.3.11(3),
printed pp.1122–1123 (PDF pp.1139–1140).
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated

variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (e : Preparation.Earlier d c)
  [IsElementaryAbelian 2 (d.componentSpan c.L)]
  (hR : d.R ≤ centralizer (d.V : Set G))
  (hMc : d.Mc = centralizer (d.Z : Set G))
  (hinter : d.M ⊓ d.Mc = (d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G))
  {r : ℕ} (h : RepeatedNatural d c.L r) (p : PlaneParabolic d c.L h.model)

include e hR hMc hinter h p in
/-- The complete residual calculation on the repeated natural module,
with both centralizers and their two-residuals in the original ambient group. -/
theorem residual_calculation :
    twoResidualAmbient (d.Yplus ⊓ centralizer (projectedCenter d c.L : Set G)) ≠ ⊥ ∧
    twoResidualAmbient (d.Yplus ⊓ centralizer (projectedCenter d c.L : Set G)) =
      twoResidualAmbient (d.Yplus ⊓ centralizer (d.Z : Set G)) ∧
    twoResidualAmbient (d.Yplus ⊓ centralizer (d.Z : Set G)) ≤
      twoResidualAmbient (d.Yplus ⊓ centralizer (d.V : Set G)) := by
  have hg := repeated_geometry_of_plane_calculations e h p
    (plane_theta_fixed_eq_zero p.plane p.dimension)
    (exists_cubic_fixing_sylow_fixed p.plane p.dimension)
  exact ⟨hg.2, projected_residual_eq e.core_le_R hR h e.yplus_le,
    center_residual_le_module_residual hMc hinter⟩

include e hR h p in
/-- The whole component span retains exactly its larger central submodule. -/
theorem fixed_space :
    d.componentSpan c.L ⊓ centralizer (d.Yplus : Set G) =
      d.componentSpan c.L ⊓ centralizer (c.L : Set G) := by
  have hg := repeated_geometry_of_plane_calculations e h p
    (plane_theta_fixed_eq_zero p.plane p.dimension)
    (exists_cubic_fixing_sylow_fixed p.plane p.dimension)
  exact span_fixed_eq_of_commutator_fixed_eq_bot e.core_le_R hR h e.yplus_le hg.1

include e hR hMc hinter h p in
/-- Both source branch choices are derived from the actual residual calculation
and the actual E₉ quotient, rather than supplied as assumptions. -/
theorem source_branches
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action ∧
      d.Yplus < d.Y ∧ OutsideStructure.SecondChoice d := by
  obtain ⟨hne, heq, _⟩ := residual_calculation e hR hMc hinter h p
  rw [heq] at hne
  have hextra := extraspecial_of_center_residual_ne_bot hMc hinter h7 hne
  exact ⟨hextra, second_choice_of_extraspecial hextra
    (Preparation.source_quotients e (Or.inl rfl) h.model).1⟩

include e hR hMc hinter h p in
/-- The repeated-natural branch of 15.3.24 is impossible under the actual
preparation output and genuine earlier local conclusions. -/
theorem repeated_natural_excluded
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) : False := by
  have hb := source_branches e hR hMc hinter h p h7
  exact contradiction_of_second_choice_and_fixed_space c hb.2.2 (fixed_space e hR h p)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated

end
