module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.ResidualRank
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.RootCentralizer
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.SylowFixers
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# The ordinary G₂ rows in original 15.2.24

The original cubic residual theorem puts K in the selected component,
including its permitted central two-covers. The marked involution descends
to a two-central element, hence a long-root element. Its full centralizer
is the first root-local subgroup, with two-core quotient PSL₂ over the
same field. This bounds its three-rank by one, contradicting m₃(K)=2.
The model calculations retain their ATLAS attribution and license.
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
private theorem g2_twoCentral_rank
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (t : Atlas.G2.Model F) (ht : orderOf t = 2)
    (hc : DoubleCoverCentralizer.TwoCentral t) :
    primeRank 3 (centralizer ({t} : Set (Atlas.G2.Model F))) ≤ 1 := by
  obtain ⟨Q,htQ,htc⟩ := hc
  obtain ⟨g,b,hb,he⟩ := Atlas.G2.EvenInvolutionGeometry.central_involution_isLongRoot
    Q htQ (ht ▸ pow_orderOf_eq_one t)
    (fun y hy => (congrArg Subtype.val (mem_center_iff.mp htc ⟨y,hy⟩)).symm)
    (by intro h; simp [h] at ht)
  let e := MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj (Atlas.G2.rootA b))
  rw [MulAut.congr_conj,MulAut.fixedSubgroup_conj,MulAut.fixedSubgroup_conj] at e
  have hgt : (MulAut.conj g) (Atlas.G2.rootA b) = t := he.symm
  rw [hgt,Atlas.G2.LieParabolicSetup.centralizer_rootA_eq_local₁ hb] at e
  rw [←primeRank_equiv 3 e]
  exact Atlas.G2.PerfectSubgroups.local₁_odd_primeRank_le_one (by decide)

/-- The full G2 central quotient is incompatible with the original marked component. -/
theorem not_g2_quotient_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (c.component ⧸ pCore 2 c.component) ≃* Atlas.G2.Model F)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  have hres := ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual.component_eq_cubic_residual_of_twoCore_model
    (Chapter3.sqtk_of_mem_H hsource.ambient hI.1) c.isComponent hF e
  obtain ⟨t,ht,htc,hr⟩ := quotient_centralizer_three_rank_of_residual d c hI hz hzne
    e hres a ha (marked_component_twoCentral d c hI hP hz hzne a ha hi)
  have hu := g2_twoCentral_rank t ht htc
  omega

/-- The literal simple G2 row, with its original field and action. -/
theorem not_g2_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
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
  apply not_g2_quotient_component d c hI hP hz hzne a ha (e := q) (hi := hi)
  rw [hF]
  exact lt_of_eq_of_lt (by decide : 2 = 2^1) (Nat.pow_lt_pow_right (by decide) hn)

/-- The permitted central two-covers of G2(4) are excluded without removing their centers. -/
theorem not_g2_four_cover_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : IsG2At (c.component ⧸ pCore 2 c.component) 4)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card (f := 2) hF
  exact not_g2_quotient_component d c hI hP hz hzne a ha (by omega) e hi

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
