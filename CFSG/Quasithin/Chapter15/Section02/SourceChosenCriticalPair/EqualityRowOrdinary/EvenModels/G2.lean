module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.G2
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.G2

/-!
# Direct G2 ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.G2. The original residual input and literal
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

/-- The full G2 central quotient is incompatible with the original marked component. -/
theorem not_g2_quotient_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (c.component ⧸ pCore 2 c.component) ≃* Atlas.G2.Model F)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  have hres := ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual.component_eq_cubic_residual_of_twoCore_model
    (Chapter3.sqtk_of_mem_H hsource.ambient hI.1) c.isComponent hF e
  obtain ⟨t,ht,htc,hr⟩ := quotient_centralizer_three_rank_of_residual r hcard c hI hz hzne
    e hres a ha (marked_component_twoCentral r hcard c hI hP hz hzne a ha hi)
  have hu := g2_twoCentral_rank t ht htc
  omega

/-- The literal simple G2 row, with its original field and action. -/
theorem not_g2_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hs : IsSimpleGroup c.component) {n : ℕ} (hn : 2 ≤ n)
    (hm : IsG2At c.component (2 ^ n))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let := hs
  let : IsQuasisimple c.component := c.isComponent.2
  have hc : pCore 2 c.component = ⊥ := c.center_eq.symm.trans center_eq_bot_of_simple_perfect
  let q : (c.component ⧸ pCore 2 c.component) ≃* Atlas.G2.Model F :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
  apply not_g2_quotient_component r hcard c hI hP hz hzne a ha (e := q) (hi := hi)
  rw [hF]
  exact lt_of_eq_of_lt (by decide : 2 = 2^1) (Nat.pow_lt_pow_right (by decide) hn)

/-- The permitted central two-covers of G2(4) are excluded without removing their centers. -/
theorem not_g2_four_cover_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : IsG2At (c.component ⧸ pCore 2 c.component) 4)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card (f := 2) hF
  exact not_g2_quotient_component r hcard c hI hP hz hzne a ha (by omega) e hi

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
