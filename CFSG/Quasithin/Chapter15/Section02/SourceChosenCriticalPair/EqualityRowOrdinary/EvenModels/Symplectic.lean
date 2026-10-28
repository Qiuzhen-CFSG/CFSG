module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Symplectic
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Symplectic

/-!
# Direct Symplectic ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.Symplectic. The original residual input and literal
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

/-- The original marked component cannot have a nonbinary symplectic central quotient. -/
theorem not_symplectic_quotient_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : (c.component ⧸ pCore 2 c.component) ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2 = 2^1) (Nat.pow_lt_pow_right (by decide) hn)
  have hres := ChapterA.Section03.OddPrime.SourceModels.SymplecticCubicResidual.component_eq_cubic_residual_of_twoCore_model
    (Chapter3.sqtk_of_mem_H hsource.ambient hI.1) c.isComponent hlarge e
  obtain ⟨t,ht,_,hr⟩ := quotient_centralizer_three_rank_of_residual r hcard c hI hz hzne
    e hres a ha (marked_component_twoCentral r hcard c hI hP hz hzne a ha hi)
  have hu := symplectic_involution_rank hF t ht
  omega

/-- The literal nonbinary PSp4 row of original 15.2.24 is impossible. -/
theorem not_symplectic_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hs : IsSimpleGroup c.component) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp c.component 2 (2 ^ n))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let := hs
  let : IsQuasisimple c.component := c.isComponent.2
  have hc : pCore 2 c.component = ⊥ := c.center_eq.symm.trans center_eq_bot_of_simple_perfect
  let q := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
  exact not_symplectic_quotient_component r hcard c hI hP hz hzne a ha hn hF q hi
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
