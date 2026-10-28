module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Preparation
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceComplete
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# The genuine E.6.8 model list in the ordinary L₃ branch

An ordinary component of C_G(U) escapes N_G(V), and its intersection with
N_G(V) centralizes V. Index two gives U = C_V(K), so the adequate E.6.8
theorem supplies every clause of the full source records in this application.
The Borel row becomes PSL₃(2), identified with PSL₂(7) by the actual matrix
isomorphism. Trivial intersection action removes the nonbinary symplectic
rows; the binary derived carrier is A₆. The remaining rank-two rows still
require the cubic-actor exclusion; this module asserts only the model list.

Source: Aschbacher–Smith, E.6.8 and 12.4.8, printed pp.247–248 and 815.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.Components
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

theorem Configuration.component_not_le_normalizer (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) :
    ¬ K ≤ normalizer (V : Set G) := by
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hg := escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape
  exact component_not_le hE (source_earlierLocalFacts hE) hg.2.2.2.1 hK

theorem Configuration.component_intersection_centralizes (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) :
    K ⊓ normalizer (V : Set G) ≤ centralizer (V : Set G) := by
  have hg := escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape
  exact (le_inf inf_le_right (inf_le_left.trans hK.1)).trans hg.2.2.1.le

theorem Configuration.component_fixed (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) :
    U = V ⊓ centralizer (K : Set G) := by
  let _ := c.chosen.elementary
  have hU := hyperplane_card c.extension c.fixed_nontrivial c.le_module c.corank
  have hV := module_card c.extension c.fixed_nontrivial
  let W := V ⊓ centralizer (K : Set G)
  have hUW : U ≤ W := le_inf c.le_module (le_centralizer_iff.mpr hK.1)
  have hcard : Nat.card W ∣ 16 := hV ▸ card_dvd_of_le (show W ≤ V from inf_le_left)
  have hge : 8 ≤ Nat.card W := hU ▸ Nat.card_le_card_of_injective (inclusion hUW) (inclusion_injective hUW)
  have hcases : Nat.card W = 8 ∨ Nat.card W = 16 := by
    have hh : Nat.card W ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hcard, by decide⟩
    have hd : Nat.divisors 16 = {1,2,4,8,16} := by decide
    rw [hd] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  rcases hcases with hw | hw
  · exact eq_of_le_of_card_ge hUW (hU.trans hw.symm).ge
  · have hWV : W = V := eq_of_le_of_card_ge inf_le_left (hV.trans hw.symm).le
    have hKC : K ≤ centralizer (V : Set G) := le_centralizer_iff.mpr
      (show V ≤ centralizer (K : Set G) from
        hWV ▸ (inf_le_right : W ≤ centralizer (K : Set G)))
    exact (c.component_not_le_normalizer hK
      (hKC.trans (Subgroup.centralizer_le_normalizer _))).elim

/-- The full E.6.8 records apply to this actual hyperplane.  The two fixed-space
fields omitted by the general adequate theorem follow here from its index two. -/
theorem Configuration.component_alternatives (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) :
    ComponentAlternatives (normalizer (V : Set G)) V U
      (sylowCentralizer (T : Subgroup G) V) K := by
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hg := escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape
  rcases RemainingSieve.adequateComponentAlternatives_knownSimple hE hg.2.2.2.1 hK with
    hb | hs | h4 | ha | ho
  · exact Or.inl hb
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl
      ⟨h4.1, h4.2.1, c.component_fixed hK, h4.2.2.1, h4.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨ho.1, c.component_fixed hK, ho.2.1, ho.2.2⟩)))

omit [Finite G] in
private theorem borel_model_one {K : Subgroup G} [IsQuasisimple K]
    (hm : BorelComponentModel K 1) : ClassicalGroup.IsPSL K 3 2 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  cases hm with
  | linear_two hn iso =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
    let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simpa using hF)
    exact (Group.IsPerfect.not_isSolvable K
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  | suzuki m hm hn iso => omega
  | linear_three hn iso => simpa using iso
  | unitary_three hn iso =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := iso
    let := BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable J
      (by simpa using hF) (by simpa using hconj)
    exact (Group.IsPerfect.not_isSolvable K
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  | linear_three_cover hn hz iso => omega

theorem Configuration.borel_component_binary (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {n : ℕ} (hb : BorelAlternative (normalizer (V : Set G)) V U K n) :
    ClassicalGroup.IsPSL K 3 2 := by
  let := hK.quasisimple
  have hbound : n ≤ 1 := c.corank ▸ hb.bound
  have hpos : 0 < n := by
    rw [hb.dimension]
    exact fixedSpace_corank_pos
      (source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial)
      (c.component_not_le_normalizer hK)
  have hn : n = 1 := by omega
  exact borel_model_one (hn ▸ hb.model)


/-- The only Borel row is the actual exceptional PSL₂(7) model. -/
theorem Configuration.borel_component_fermatMersenne (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {n : ℕ} (hb : BorelAlternative (normalizer (V : Set G)) V U K n) :
    ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := c.borel_component_binary hK hb
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let d := (e.trans (Atlas.fieldEquivPSL 3 (FiniteField.ringEquivOfCardEq hcard))).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm
  exact ⟨7,⟨by decide,Or.inr ⟨3,by decide⟩⟩,
    ZMod 7,inferInstance,inferInstance,by simp,⟨d⟩⟩

/-- Trivial action of the component intersection removes every nonbinary
symplectic row. The binary derived carrier is identified with the actual A₆. -/
theorem Configuration.symplectic_component_six (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {n : ℕ} (hs : SymplecticAlternative (normalizer (V : Set G)) V U K n) :
    Chapter1.Section02.LocalModels.IsAlternating K 6 := by
  have hn : n = 1 := by
    have hlow := hs.model.1
    by_contra hne
    have hn : 1 < n := by omega
    have hd := (hs.decomposition hn).1
    have hc : ⁅V,K ⊓ normalizer (V : Set G)⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mpr (c.component_intersection_centralizes hK))
    rw [hc,bot_sup_eq,← c.component_fixed hK] at hd
    have hu := hyperplane_card c.extension c.fixed_nontrivial c.le_module c.corank
    have hv := module_card c.extension c.fixed_nontrivial
    rw [hd,hv] at hu
    omega
  obtain ⟨_,F,_,_,hc,⟨e⟩⟩ := hs.model
  rw [hn,pow_one] at hc
  exact ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hc)⟩

/-- The literal E.6.8 reduction before the cubic actor excludes the remaining
rank-two models. Every family is expressed by an actual model isomorphism. -/
theorem Configuration.component_model_list (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) :
    (∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p) ∨
      Chapter1.Section02.LocalModels.IsAlternating K 6 ∨
      ClassicalGroup.IsPSL K 4 2 ∨
      (Chapter1.Section02.LocalModels.IsAlternating K 7 ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover K 6 ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover K 7) ∨
      ClassicalGroup.IsPSL K 3 3 ∨ Nonempty (K ≃* Sporadic.Mathieu.M11) := by
  rcases c.component_alternatives hK with ⟨n,hb⟩ | ⟨n,hs⟩ | h4 | ha | ho
  · exact Or.inl (c.borel_component_fermatMersenne hK hb)
  · exact Or.inr (Or.inl (c.symplectic_component_six hK hs))
  · exact Or.inr (Or.inr (Or.inl h4.model))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha.model)))
  · rcases ho.model with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
