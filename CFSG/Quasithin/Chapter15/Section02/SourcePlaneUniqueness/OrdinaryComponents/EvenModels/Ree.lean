module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Intersection
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.SolvableSylowThreeFree

/-!
# Excluding the ordinary Ree component in original 15.2.24

The native A.3.18 residual theorem places K in the actual component.
Consequently H intersect L is solvable, contains a full Sylow two-subgroup,
and has three-rank at least two. The Ree solvable-Sylow theorem makes
its order prime to three, including through the original central two-kernel.
Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

include d
/-- The actual Ree component is excluded by its solvable full-Sylow intersection with H. -/
theorem not_ree_quotient_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (c.component ⧸ pCore 2 c.component) ≃* ReeF4.Model m) : False := by
  let eZ := (QuotientGroup.quotientMulEquivOfEq c.center_eq).trans e
  have hres := (ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual.component_eq_primeClosure_and_residual
    (Chapter3.sqtk_of_mem_H hsource.ambient hI.1) c.isComponent c.center_two hm eZ).2
  obtain ⟨Q,hQ⟩ := component_intersection_sylow d c hP
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.component))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hc := ReeF4.Parabolics.coprime_three_of_solvable_sylow_overgroup_of_two_kernel
    hm f hf hk Q (componentIntersection (H := H) c) (component_intersection_solvable d c) hQ
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr (Nat.prime_three.coprime_iff_not_dvd.mp hc)
  have hr := component_intersection_three_rank d c hI hres
  omega

/-- The exact original simple Ree row, retaining the given root-data model. -/
theorem not_ree_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hs : IsSimpleGroup c.component) {m : ℕ} (hm : 1 ≤ m)
    (he : Chapter1.Section02.LocalModels.IsReeF4At c.component m) : False := by
  obtain ⟨r,⟨e⟩⟩ := he
  let := hs
  let : IsQuasisimple c.component := c.isComponent.2
  have hc : pCore 2 c.component = ⊥ := c.center_eq.symm.trans center_eq_bot_of_simple_perfect
  let q := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans
    (e.trans r.modelEquiv)
  exact not_ree_quotient_component d c hI hP hm q

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
