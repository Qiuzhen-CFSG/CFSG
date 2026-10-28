module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Bender
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Bender

/-!
# Direct Bender ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.Bender. The original residual input and literal
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
include r hcard

/-- All three Bender rows are impossible on the original minimal escaping component. -/
theorem not_bender_component
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hs : IsSimpleGroup c.component) (hm : IsBenderModel c.component)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  let := hs
  have hai := marked_component_twoCentral r hcard c hI.1 hP hz hzne a ha hi
  obtain ⟨_,ho,Q,hQ⟩ := hai
  have hQfix : (Q : Subgroup c.component) ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hQ ⟨x,hx⟩)
  have hproper : a.fixedSubgroup ≠ ⊤ := by
    intro he
    have ha1 : a=1 := by
      apply MulEquiv.ext
      intro x
      exact (MulAut.mem_fixedSubgroup _ _).mp (he ▸ mem_top x)
    rw [ha1,orderOf_one] at ho
    omega
  have hn := bender_proper_sylow_overgroup_normalizes hm Q a.fixedSubgroup hQfix hproper
  have hfix := marked_component_borel_fixed r hcard c hI hP hz hzne a ha ⟨hi,ho,Q,hQ⟩ Q hQfix hn
  have ha1 := bender_borel_fixer hm Q a (ho ▸ pow_orderOf_eq_one a) hfix
  rw [ha1,orderOf_one] at ho
  omega
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
