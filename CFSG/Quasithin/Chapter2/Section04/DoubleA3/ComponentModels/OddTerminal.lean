module
public import Theory.SpecificGroups.PSL2.CubicActorParameter
public import Theory.SpecificGroups.PSL2.SeventeenFourGeometry
public import Theory.SpecificGroups.PSL3Three.FourNormalizer
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.OddPrime
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ModuleAbsorption
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSylowFour
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.BlockAbsorption
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
/-!
# The odd rows of the original paired-cubic component inspection

The actual first four-group is contained in the centerless component. The
source Sylow intersection lies in R, so it normalizes this four-group.
In PSL₂(17) and PSL₃(3), a two-subgroup normalizing a four-group has order
at most eight, whereas a Sylow two-subgroup has order sixteen. These two
rows are therefore excluded. The previously proved prime parameter bound
leaves PSL₂(7), identified with PSL₃(2), and the source absorption theorem
places the whole original cubic block in that component.

The final theorem is the complete odd model-action branch of 2.4.32; it
retains the literal involution centralizer, Sylow, coordinates, marked
action and odd-core hypothesis supplied by the original source setup.

Source: Aschbacher–Smith, 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.DoubleA3
local instance oddTerminal_prime_seventeen : Fact (Nat.Prime 17) := ⟨by decide⟩

private theorem map_kleinFour {K X : Type*} [Group K] [Group X]
    (e : K ≃* X) (U : Subgroup K) [IsKleinFour U] : IsKleinFour (U.map e.toMonoidHom) := by
  let f := U.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨(Nat.card_congr f.toEquiv).symm.trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv f.symm).trans IsKleinFour.exponent_two⟩

private theorem map_sylow_normalizes {K X : Type*} [Group K] [Group X]
    [Finite K]
    (e : K ≃* X) (U : Subgroup K) (P : Sylow 2 K)
    (hn : (P : Subgroup K) ≤ normalizer (U : Set K)) :
    ((P.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup X) ≤
      normalizer (U.map e.toMonoidHom : Set X) := by
  rw [←map_equiv_normalizer_eq]
  exact map_mono hn

private theorem seventeen_normal_four_false
    {K : Type*} [Group K] [Finite K]
    (e : K ≃* PSL(2,ZMod 17)) (U : Subgroup K) [IsKleinFour U]
    (P : Sylow 2 K) (hn : (P : Subgroup K) ≤ normalizer (U : Set K)) : False := by
  let V := U.map e.toMonoidHom
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsKleinFour V := map_kleinFour e U
  have hbound := Theory.PSL2.two_subgroup_normalizing_selfCentral_four_card_le_eight
    V P' (Theory.PSL2.FourNormalizer.four_centralizer
      (K := ZMod 17) ⟨17,1,by decide,by decide,by decide,by
        rw [Nat.card_zmod, pow_one]⟩ V)
    P'.isPGroup' (map_sylow_normalizes e U P hn)
  obtain ⟨f⟩ := Theory.PSL2.SeventeenGeometry.sylow_equiv_dihedral_sixteen P'
  have hcard : Nat.card P' = 16 := (Nat.card_congr f.toEquiv).trans (by
    rw [DihedralGroup.nat_card])
  omega

private theorem pslThree_three_normal_four_false
    {K : Type*} [Group K] [Finite K]
    (e : K ≃* Matrix.PSL3Three.PSL) (U : Subgroup K) [IsKleinFour U]
    (P : Sylow 2 K) (hn : (P : Subgroup K) ≤ normalizer (U : Set K)) : False := by
  let V := U.map e.toMonoidHom
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsKleinFour V := map_kleinFour e U
  let : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hbound := Theory.PSL2.two_subgroup_normalizing_selfCentral_four_card_le_eight
    V P' (Matrix.PSL3Three.centralizer_four V inferInstance IsKleinFour.card_four)
    P'.isPGroup' (map_sylow_normalizes e U P hn)
  have hcard : Nat.card P' = 16 := by
    rw [P'.card_eq_multiplicity,Matrix.PSL3Three.card_PSL]
    decide +kernel
  omega

open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The actual marked PSL₂(17) row is impossible in the paired-cubic source. -/
theorem SourceCentralizerGeometry.seventeen_component_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (e : K ≃* PSL(2,ZMod 17)) : False := by
  have hz : center K = ⊥ := by
    apply (center K).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,GorensteinWalter.psl2_center_eq_bot _,card_bot]
  have hU := g.first_module_le_component hG h K hK α hα hinner hz
  let : K.Normal := g.component_normal_of_first_module h K hK hU
  obtain ⟨P,_,he,hc,_,hn,_⟩ := g.component_sylow_normal_four K hz hU
  let U := (c.U₁.subgroupOf (involutionCentralizer g.z₂)).subgroupOf K
  let : IsElementaryAbelian 2 U := he
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    have hh : Nat.card U = 4 := hc
    omega)
  let : IsKleinFour U := ⟨hc,IsElementaryAbelian.exponent_eq_prime⟩
  exact seventeen_normal_four_false e U P hn

/-- The actual marked PSL₃(3) row is impossible in the paired-cubic source. -/
theorem SourceCentralizerGeometry.pslThree_three_component_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (e : K ≃* Matrix.PSL3Three.PSL) : False := by
  have hz : center K = ⊥ := by
    apply (center K).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr (e.trans Matrix.PSL3Three.equiv.symm)).toEquiv,
      Matrix.PSL3Three.center_eq_bot,card_bot]
  have hU := g.first_module_le_component hG h K hK α hα hinner hz
  let : K.Normal := g.component_normal_of_first_module h K hK hU
  obtain ⟨P,_,he,hc,_,hn,_⟩ := g.component_sylow_normal_four K hz hU
  let U := (c.U₁.subgroupOf (involutionCentralizer g.z₂)).subgroupOf K
  let : IsElementaryAbelian 2 U := he
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    have hh : Nat.card U = 4 := hc
    omega)
  let : IsKleinFour U := ⟨hc,IsElementaryAbelian.exponent_eq_prime⟩
  exact pslThree_three_normal_four_false e U P hn

/-- The odd model-action alternative of 1.1.5 contributes exactly the
retained PSL₃(2) row to the original 2.4.32 component inspection. -/
theorem SourceCentralizerGeometry.odd_component_action_model
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hmodel : ClassicalGroup.IsPSL K 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range) :
    Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
  rcases hmodel with hm | ⟨p,hp,hm⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let f : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    exact (g.pslThree_three_component_action_false hG h K hK α hα hinner
      (e.trans (Atlas.fieldEquivPSL 3 f))).elim
  · have hs := g.odd_prime_marked_parameter hG h K hK α hα hinner hp hm
    rcases hs with rfl | rfl
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hF)⟩
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let f : F ≃+* ZMod 17 := FiniteField.ringEquivOfCardEq (by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      exact (g.seventeen_component_action_false hG h K hK α hα hinner
        (e.trans (Atlas.fieldEquivPSL 2 f))).elim

/-- The original odd model-action family supplies the full 2.4.32 conclusion
for the retained binary linear-three component. -/
theorem SourceCentralizerGeometry.odd_component_action_source32
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hmodel : ClassicalGroup.IsPSL K 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range) :
    d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype ∧
      Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨e⟩ := g.odd_component_action_model hG h K hK α hα hmodel hinner
  exact ⟨g.linear_three_two_absorbs_first_block hG h K hK α hα hinner ho e,⟨e⟩⟩
end CFSG.Quasithin.Chapter2.DoubleA3
