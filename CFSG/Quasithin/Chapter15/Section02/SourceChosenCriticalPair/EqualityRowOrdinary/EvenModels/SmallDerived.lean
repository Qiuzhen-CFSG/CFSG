module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.SmallDerived
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.SmallDerived

/-!
# Direct SmallDerived ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.SmallDerived. The original residual input and literal
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

private theorem not_centerless_model_of_fixed_rank
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hi : a ∈ (MulAut.conj (G := c.component)).range)
    {D : Type*} [Group D] [Finite D] (e : c.component ≃* D)
    (hc : center D = ⊥) (hr : 2 ≤ primeRank 3 D)
    (ho : IsPGroup 2 (MulAut.Outer D))
    (hf : ∀ t : D, orderOf t = 2 → TwoCentral t →
      primeRank 3 (centralizer ({t} : Set D)) ≤ 1) : False := by
  have hcenter : center c.component = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center D at hh
    rw [hc,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hcore : pCore 2 c.component = ⊥ := c.center_eq.symm.trans hcenter
  let q : (c.component ⧸ pCore 2 c.component) ≃* D :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e
  obtain ⟨t,ht,htc,hlow⟩ := r.quotient_centralizer_three_rank_direct c hcard hI hz hzne q hr ho a ha
    (marked_component_twoCentral r hcard c hI hP hz hzne a ha hi)
  have hu := hf t ht htc
  omega

/-- The actual Sp4(2) derived row of15.2.24 is impossible. -/
theorem not_symplectic_derived_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : Nonempty (c.component ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨e⟩ := hm
  let f := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  have facts := Theory.SpecificGroups.BinaryComponentResidual.alternatingSix
  exact not_centerless_model_of_fixed_rank r hcard c hI hP hz hzne a ha hi f
    facts.1 facts.2.1 facts.2.2 (fun t ht _ => six_involution_rank t ht)

/-- The two-central Tits row of15.2.24 is impossible. -/
theorem not_tits_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : Nonempty (c.component ≃* Tits.ParrottGroup))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨e⟩ := hm
  apply not_centerless_model_of_fixed_rank r hcard c hI hP hz hzne a ha hi e
    (Tits.RelativeSylowMarking.center_eq_bot Tits.parrottFiniteImageEquiv) ?_
    Tits.OuterOddSubgroups.parrott_outer_isPGroup tits_twoCentral_rank
  rw [primeRank_equiv 3 Tits.parrottFiniteImageEquiv]
  exact Tits.ThreeRank.rank_two_le

/-- The actual G2(2) derived row of15.2.24 is impossible. -/
theorem not_g2_derived_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : Nonempty (c.component ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨e⟩ := hm
  have facts := Theory.SpecificGroups.BinaryComponentResidual.g2
  exact not_centerless_model_of_fixed_rank r hcard c hI hP hz hzne a ha hi e
    facts.1 facts.2.1 facts.2.2 (fun t ht _ => g2_derived_involution_rank t ht)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
