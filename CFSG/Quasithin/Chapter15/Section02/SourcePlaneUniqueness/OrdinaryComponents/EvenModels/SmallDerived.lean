module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryLinear
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.QuotientRank
public import Theory.SpecificGroups.Tits.SylowCenterMaximal
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound
public import Theory.SpecificGroups.Tits.OuterOddSubgroups
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.SpecificGroups.G2.BinaryResidualCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvolutionCentralizer
public import Theory.GroupTheory.OddKernelInvolutionCentralizer

/-!
# The three small derived ordinary component rows in15.2.24

The actual Sp4(2)' carrier is A6, whose involution centralizers have no
factor nine. The actual G2(2)' carrier has one involution class, with
centralizer of order96. For Tits, the source Sylow marking identifies the
inner involution with the certified Sylow-central involution; its centralizer
has order10240. In each case the centralizer has three-rank at most one.

A.3.18 puts the original rank-two K inside the same fixed subgroup, giving
the contradiction on the original ordinary component. The full native
model equivalences, central quotients and action markings are preserved.
Source: Aschbacher--Smith,15.2.24, printed p.1117, refs/quasithin.pdf.
The imported model calculations retain their ATLAS and Parrott attribution.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open DoubleCoverCentralizer

private theorem six_involution_rank (t : alternatingGroup (Fin 6)) (ht : orderOf t = 2) :
    primeRank 3 (centralizer ({t} : Set (alternatingGroup (Fin 6)))) ≤ 1 := by
  let s : Equiv.Perm (Fin 6) := t
  have hs : orderOf s = 2 := (Subgroup.orderOf_coe t).trans ht
  have hp : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hcy := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
  have hsum := s.sum_cycleType_le
  rw [hcy,Multiset.sum_replicate] at hsum
  have hpos : 0 < s.cycleType.card := by
    apply Nat.pos_of_ne_zero
    intro h
    have he : s = 1 := Equiv.Perm.cycleType_eq_zero.mp (Multiset.card_eq_zero.mp h)
    simp [he] at hs
  have hb : s.cycleType.card ≤ 3 := by
    simp only [nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hsum
    omega
  have hcases : s.cycleType.card = 1 ∨ s.cycleType.card = 2 ∨ s.cycleType.card = 3 := by omega
  have hnine : ¬9 ∣ Nat.card (centralizer ({s} : Set (Equiv.Perm (Fin 6)))) := by
    rw [Equiv.Perm.nat_card_centralizer,hcy]
    rcases hcases with h | h | h <;> rw [h] <;> norm_num [Nat.factorial]
  let f := (alternatingGroup (Fin 6)).subtype.elementCentralizerMap t
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : centralizer ({s} : Set (Equiv.Perm (Fin 6))) => v.val) h
  exact (_root_.primeRank_le_of_injective 3 f hf).trans (primeRank_le_of_prime_pow_not_dvd hnine)

private theorem tits_twoCentral_rank (t : Tits.ParrottGroup) (ht : orderOf t = 2)
    (hc : TwoCentral t) : primeRank 3 (centralizer ({t} : Set Tits.ParrottGroup)) ≤ 1 := by
  obtain ⟨R,htR,hct⟩ := hc
  obtain ⟨e,he⟩ := Tits.RelativeSylowMarking.exists_sylow_marking Tits.parrottFiniteImageEquiv R
  have htc : t ∈ centralizer (R : Set Tits.ParrottGroup) := by
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hct ⟨x,hx⟩)
  have hne : t ≠ 1 := by intro h; rw [h,orderOf_one] at ht; omega
  have hmark := Tits.RelativeSylowMarking.image_eq_r5_of_sylow_center e R he htR htc hne
  have hcard : Nat.card (centralizer ({t} : Set Tits.ParrottGroup)) = 10240 := by
    have hh := Nat.card_congr (MulAut.fixedSubgroupCongr e (MulAut.conj t)).toEquiv
    rw [MulAut.congr_conj,MulAut.fixedSubgroup_conj,MulAut.fixedSubgroup_conj] at hh
    rw [hh,hmark,
      ←Tits.RelativeParabolicNormalizers.first_eq_centralizer]
    exact Tits.ExceptionalParabolics.first_card
  exact primeRank_le_of_prime_pow_not_dvd (by rw [hcard]; decide)

private theorem g2_derived_involution_rank
    (t : commutator (Atlas.G2.Model (ZMod 2))) (ht : orderOf t = 2) :
    primeRank 3 (centralizer ({t} : Set (commutator (Atlas.G2.Model (ZMod 2))))) ≤ 1 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (Atlas.G2.BinaryResidualCover.derived_involutions_isConj
    t Atlas.G2.BinaryParabolicPair.derivedInvolution ht
    Atlas.G2.BinaryParabolicPair.derivedInvolution_order)
  have he : (MulAut.conj g) t = Atlas.G2.BinaryParabolicPair.derivedInvolution := hg
  have hh := Nat.card_congr (MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj t)).toEquiv
  rw [MulAut.congr_conj,he,MulAut.fixedSubgroup_conj,MulAut.fixedSubgroup_conj,
    Atlas.G2.BinaryParabolicPair.centralizer_derivedInvolution_eq_first,
    Atlas.G2.BinaryParabolicPair.card_derivedFirst] at hh
  exact primeRank_le_of_prime_pow_not_dvd (by rw [hh]; decide)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

private theorem not_centerless_model_of_fixed_rank
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
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
  obtain ⟨t,ht,htc,hlow⟩ := quotient_centralizer_three_rank d c hI hz hzne q hr ho a ha
    (marked_component_twoCentral d c hI hP hz hzne a ha hi)
  have hu := hf t ht htc
  omega

/-- The actual Sp4(2) derived row of15.2.24 is impossible. -/
theorem not_symplectic_derived_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : Nonempty (c.component ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨e⟩ := hm
  let f := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  have facts := Theory.SpecificGroups.BinaryComponentResidual.alternatingSix
  exact not_centerless_model_of_fixed_rank d c hI hP hz hzne a ha hi f
    facts.1 facts.2.1 facts.2.2 (fun t ht _ => six_involution_rank t ht)

/-- The two-central Tits row of15.2.24 is impossible. -/
theorem not_tits_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : Nonempty (c.component ≃* Tits.ParrottGroup))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨e⟩ := hm
  apply not_centerless_model_of_fixed_rank d c hI hP hz hzne a ha hi e
    (Tits.RelativeSylowMarking.center_eq_bot Tits.parrottFiniteImageEquiv) ?_
    Tits.OuterOddSubgroups.parrott_outer_isPGroup tits_twoCentral_rank
  rw [primeRank_equiv 3 Tits.parrottFiniteImageEquiv]
  exact Tits.ThreeRank.rank_two_le

/-- The actual G2(2) derived row of15.2.24 is impossible. -/
theorem not_g2_derived_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : Nonempty (c.component ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨e⟩ := hm
  have facts := Theory.SpecificGroups.BinaryComponentResidual.g2
  exact not_centerless_model_of_fixed_rank d c hI hP hz hzne a ha hi e
    facts.1 facts.2.1 facts.2.2 (fun t ht _ => g2_derived_involution_rank t ht)

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
