module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.ResidualRank
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticCubicResidual
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootSocle
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.RootComponents

/-!
# The ordinary symplectic rows in original 15.2.24

A.3.18 identifies the actual component with O^{3′}(I), so K embeds in
its marked involution centralizer. Every symplectic involution centralizer
has three-rank at most one: root classes have two-kernel SL₂ quotients,
and the remaining c₂ class has a two-group centralizer. The original
rank-two K contradicts this bound. The original field and quotient maps
are retained, and no involution-classification premise remains.
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
variable {D : Type*} [Group D] [Finite D]
include d
omit d in
private theorem symplectic_involution_rank
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (t : Theory.SpecificGroups.SymplecticFour.Sp F) (ht : orderOf t = 2) :
    primeRank 3 (centralizer ({t} : Set (Theory.SpecificGroups.SymplecticFour.Sp F))) ≤ 1 := by
  by_cases hr : Theory.SpecificGroups.SymplecticFour.InvolutionTypes.IsRootElement t
  · rcases Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.root_centralizer_equiv_local
      t hr with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [primeRank_equiv 3 e]
      exact Theory.SpecificGroups.SymplecticFour.pointLocal_odd_primeRank_le_one (by decide)
    · rw [primeRank_equiv 3 e]
      exact Theory.SpecificGroups.SymplecticFour.planeLocal_odd_primeRank_le_one (by decide)
  · have hp := Theory.SpecificGroups.SymplecticFour.TwoConjugate.isPGroup_centralizer_of_nonroot_involution
      hF t ht hr
    have hz : primeRank 3 (centralizer ({t} : Set (Theory.SpecificGroups.SymplecticFour.Sp F))) = 0 := by
      apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
      obtain ⟨k,hk⟩ := hp.exists_card_eq
      rw [hk]
      exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
    omega

/-- The original marked component cannot have a nonbinary symplectic central quotient. -/
theorem not_symplectic_quotient_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
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
  obtain ⟨t,ht,_,hr⟩ := quotient_centralizer_three_rank_of_residual d c hI hz hzne
    e hres a ha (marked_component_twoCentral d c hI hP hz hzne a ha hi)
  have hu := symplectic_involution_rank hF t ht
  omega

/-- The literal nonbinary PSp4 row of original 15.2.24 is impossible. -/
theorem not_symplectic_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
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
  exact not_symplectic_quotient_component d c hI hP hz hzne a ha hn hF q hi
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
