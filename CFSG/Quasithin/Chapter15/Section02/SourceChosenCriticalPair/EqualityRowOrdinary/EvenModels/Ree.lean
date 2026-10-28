module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Ree
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Ree

/-!
# Direct Ree ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.Ree. The original residual input and literal
marked Sylow supply its geometric hypotheses without a partner residual identity.
The deliberate private import keeps those existing model lemmas internal.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
open Section01 Section03 Candidates.ComponentStructure ClassificationModels OrdinaryComponents
open BinaryLinear BinaryLinear.OuterCyclic BinaryNaturalDual.VectorStabilizers
open ChapterB.QuasisimpleSource.NaturalDualCentralizer DoubleCoverCentralizer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
variable (hcard : Nat.card (centralInvolutions T) = 2)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include r
omit hcard

/-- The actual Ree component is excluded by its solvable full-Sylow intersection with H. -/
theorem not_ree_quotient_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (c.component ⧸ pCore 2 c.component) ≃* ReeF4.Model m) : False := by
  let eZ := (QuotientGroup.quotientMulEquivOfEq c.center_eq).trans e
  have hres := (ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual.component_eq_primeClosure_and_residual
    (Chapter3.sqtk_of_mem_H hsource.ambient hI.1) c.isComponent c.center_two hm eZ).2
  obtain ⟨Q,hQ⟩ := component_intersection_sylow r c hP
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.component))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hc := ReeF4.Parabolics.coprime_three_of_solvable_sylow_overgroup_of_two_kernel
    hm f hf hk Q (componentIntersection (H := H) c) (component_intersection_solvable r c) hQ
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr (Nat.prime_three.coprime_iff_not_dvd.mp hc)
  have hr := component_intersection_three_rank r c hI hres
  omega

/-- The exact original simple Ree row, retaining the given root-data model. -/
theorem not_ree_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hs : IsSimpleGroup c.component) {m : ℕ} (hm : 1 ≤ m)
    (he : Chapter1.Section02.LocalModels.IsReeF4At c.component m) : False := by
  obtain ⟨rd,⟨e⟩⟩ := he
  let := hs
  let : IsQuasisimple c.component := c.isComponent.2
  have hc : pCore 2 c.component = ⊥ := c.center_eq.symm.trans center_eq_bot_of_simple_perfect
  let q := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans
    (e.trans rd.modelEquiv)
  exact not_ree_quotient_component r c hI hP hm q

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
