module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearBlockCubic
public import Theory.SpecificGroups.PSL3Two.Parabolics.CubicLength
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ShortBlockBudget
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.ResidualBound
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds

/-!
# Excluding the original short-block alternative in the linear amalgam

A cubic of the original second vertex moves its two-core above the full
join kernel: the actual quotient is an index-seven S₄ parabolic in L₃(2),
with self-centralizing four-core. The already proved omega-module theorem
provides two further cubic contributions. Restriction to the literal
two-residual converts the source's three-chief-factor budget into the
full-core budget required by LinearBlockExclusion.

For the source application the cubic is constructed inside B, and the
three-factor bound is proved from the short-block hypothesis and the
original second-parabolic marking. The identity K₂=L₂ is retained literally.
This excludes 13.2.2(10II) in the linear branch of 13.4.7(4), without any
supplied movement or numerical chief-count premise. The preceding
trichotomy, residual movement, remaining model alternatives and universal
PlaneAmalgamSource1347 remain to be proved.
Source: Aschbacher–Smith 13.4.7(4), printed pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

omit hres in
/-- A cubic in the original second vertex contributes above the original join's
full two-core, through the actual linear quotient. -/
theorem original_pair_linear_outer_cubic_length
    (E : Subgroup (A ⊔ B : Subgroup G)) (hE : Nat.card E = 3)
    (hEB : E ≤ B.subgroupOf (A ⊔ B)) :
    1 ≤ sectionCubicLength E (pCore 2 (A ⊔ B : Subgroup G))
      ((B.pCoreIn 2).subgroupOf (A ⊔ B)) := by
  let X := A ⊔ B
  let S : Sylow 2 X := T.subtype (hTA.trans le_sup_left)
  let P := B.subgroupOf X
  obtain ⟨e⟩ := original_pair_linear_full_quotient h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  let f := (e.trans Matrix.PSL3Two.equiv.symm).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f :=
    (e.trans Matrix.PSL3Two.equiv.symm).surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (e.trans Matrix.PSL3Two.equiv.symm).injective,QuotientGroup.ker_mk']
  have hi : P.index = 7 := by
    have hc : Nat.card ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) = 168 :=
      (Nat.card_congr eK.toEquiv).trans Matrix.PSL3Two.card_PSL
    have hh := (original_pair_parabolic_index_formula h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).2
    change P.index * 3 * 2 ^
      (Nat.card ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype))).factorization 2 = _ at hh
    rw [hc,show (Nat.factorization 168) 2 = 3 from by decide +kernel] at hh
    omega
  have hcore : P.pCoreIn 2 = (B.pCoreIn 2).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_pCoreIn_of_injective 2 P X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le (show B ≤ X from le_sup_right),
      map_subgroupOf_eq_of_le ((B.pCoreIn_le 2).trans (show B ≤ X from le_sup_right))]
  have hh := Matrix.PSL3Two.index_seven_core_section_pos f hf (hk ▸ pCore_isPGroup)
    S P (fun _ ht => hTB ht) hi E hE hEB
  rwa [hk,hcore] at hh

/-- The original linear block obstruction needs only its literal residual chief
budget and the source maximum-family inclusion. The cubic and both movement
contributions are constructed here. -/
theorem original_pair_linear_residual_chief_budget_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hfamily : elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G))
    (t : ChiefSeries ((pResidual 2 B).map B.subtype))
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) (ht : t.noncentralTwoCount ≤ 3) : False := by
  let X := A ⊔ B
  have hd : 3 ∣ Nat.card B := by
    rw [SymmetricThreeTwoCore.card_eq eB]
    exact dvd_mul_of_dvd_left (by decide : 3 ∣ 6) _
  obtain ⟨E₀,hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 3
    (n := 1) (by simpa using hd)
  let j := inclusion (show B ≤ X from le_sup_right)
  let E := E₀.map j
  have hj : Function.Injective j := inclusion_injective _
  have hE : Nat.card E = 3 := (card_map_of_injective hj).trans (by simpa using hE₀)
  have hEB : E ≤ B.subgroupOf X := by
    rintro x ⟨a,ha,rfl⟩
    exact a.property
  let eR := (pResidual 2 B).equivMapOfInjective B.subtype B.subtype_injective
  let t₀ := t.mapActor eR.symm
  have ht₀ := t.mapActor_complete eR.symm ht0 ht1
  have hb := NoncentralChiefRefinement.CubicComparison.symmetricThree_core_length_le_residual_count
    eB E₀ (by simpa using hE₀) t₀ ht₀.1 ht₀.2
  have hc : conjugationCubicLength E₀ (pCore 2 B) ≤ 3 :=
    hb.trans ((t.mapActor_noncentralTwoCount eR.symm).le.trans ht)
  have hcore : (pCore 2 B).map j = (B.pCoreIn 2).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le
      ((B.pCoreIn_le 2).trans (show B ≤ X from le_sup_right))]
    rfl
  have hbudget : conjugationCubicLength E ((B.pCoreIn 2).subgroupOf X) ≤ 3 := by
    rw [←hcore,NoncentralChiefRefinement.CubicComparison.length_map_injective j hj]
    exact hc
  exact original_pair_linear_block_budget_impossible h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    hfamily E hE hbudget (original_pair_linear_outer_cubic_length h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK eK E hE hEB)


/-- The source block alternative is impossible for the original linear join
when its second residual is literally the marked L₂. -/
theorem original_pair_linear_short_block_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hb : ChapterC.IsShort L)
    (hfamily : elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G))
    (J : Subgroup G) (hJL : J ≤ L)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      Theory.SpecificGroups.SymmetricSix.synthemeStabilizer ⊓ alternatingGroup (Fin 6))
    (hK₂ : (pResidual 2 B).map B.subtype = (pResidual 2 J).map J.subtype) : False := by
  have hc : ∃ s : ChiefSeries ((pResidual 2 B).map B.subtype),
      s.head = ⊥ ∧ s.last = ⊤ ∧ s.noncentralTwoCount ≤ 3 := by
    rw [hK₂]
    obtain ⟨s⟩ := SeriesOn.exists_series (⊤ : Subgroup ((pResidual 2 J).map J.subtype))
    exact ⟨s.series,s.head_eq,s.last_eq,
      second_parabolic_residual_short_chief_budget D m hb J hJL hTJ himage
        s.series s.head_eq s.last_eq⟩
  obtain ⟨s,hs0,hs1,hs⟩ := hc
  exact original_pair_linear_residual_chief_budget_impossible h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    hfamily s hs0 hs1 hs

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
