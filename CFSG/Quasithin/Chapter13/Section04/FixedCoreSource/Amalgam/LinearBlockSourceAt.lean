module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearBlockSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearBlockCubicAt

/-!
# The guarded original linear short-block exclusion

Construct a cubic in the actual second vertex and combine its outer
contribution with both omega contributions. Original shortness gives
the three-factor bound on the literal two-residual K2=L2, contradicting
the movement bound. No cubic or chief-budget premise is supplied.
Source: Aschbacher--Smith 13.4.7(4), printed pp.902--903.
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

/-- The original linear block obstruction needs only its literal residual chief
budget and the source maximum-family inclusion. The cubic and both movement
contributions are constructed here. -/
theorem original_pair_linear_residual_chief_budget_impossible_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  exact original_pair_linear_block_budget_impossible_at h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    hfamily E hE hbudget (original_pair_linear_outer_cubic_length h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK eK E hE hEB)


/-- The source block alternative is impossible for the original linear join
when its second residual is literally the marked L₂. -/
theorem original_pair_linear_short_block_impossible_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  exact original_pair_linear_residual_chief_budget_impossible_at h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    hfamily s hs0 hs1 hs

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
