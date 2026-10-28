module
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import Theory.SpecificGroups.SymmetricFive.WreathTwoCore
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Extracting and promoting the replacement component

The literal symmetric-five wreath quotient supplies an actual local
C-component with A₅ two-core quotient and index-two Sylow stabilizer.
A reduced module moved by this component makes its intrinsic module
nontrivial. Finally, invariance of its Sylow orbit in every maximal
two-local overgroup makes the component maximal in the ambient local family.

These are the subgroup and quotient deductions in the final paragraph of
Aschbacher--Smith §10.3, printed pp.756--757. Recognition of the wreath
quotient and the overgroup invariance are separate source inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Theory.SpecificGroups.SymmetricFive.WreathComponents
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Transport the actual quotient and stabilizer through the inclusion in G. -/
theorem component_of_wreath {J K : Subgroup G}
    (hTJ : (T : Subgroup G) ≤ J) (hcore : J.pCoreIn 2 ≠ ⊥)
    (e : (J ⧸ pCore 2 J) ≃* W) (hK : K ∈ Chapter1.cComponentsIn J) :
    K ∈ Chapter1.L G (T : Subgroup G) ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
  let S := T.subtype hTJ
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent hcore
      ⟨S, map_subgroupOf_eq_of_le hTJ⟩ hK.1 hK.2
  let a := subgroupOfEquivOfLe hK.1
  obtain ⟨b⟩ := (wreath_quotient_component e hK.2).1
  let bG : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans b
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  refine ⟨hlocal, IsQuasisimple.of_mulEquiv bG.symm, ⟨bG⟩, ?_⟩
  intro hn
  have hN : (S : Subgroup J) ≤ normalizer (K.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hK.1]
    exact comap_mono hn
  have hi := (wreath_quotient_component e hK.2).2
  have hd := index_dvd_of_le hN
  rw [hi] at hd
  exact S.not_dvd_index hd

/-- A literal wreath quotient supplies a component; none is assumed as data. -/
theorem exists_component_of_wreath {J : Subgroup G}
    (e : (J ⧸ pCore 2 J) ≃* W) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn J := by
  obtain ⟨A, hA⟩ := exists_isCComponent_of_not_isSolvable
    (wreath_quotient_not_solvable e)
  refine ⟨A.map J.subtype, map_subtype_le A, ?_⟩
  simpa only [subgroupOf, comap_map_eq_self_of_injective J.subtype_injective] using hA

/-- An actual reduced normal module outside whose centralizer K lies
forces the intrinsic A.4 module of K to be nontrivial. -/
theorem faithful_of_reduced_movement {C K U : Subgroup G}
    (hE : IsEvenCharacteristicAt T)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G))
    (hKC : K ∈ Chapter1.cComponentsIn C) (hUC : U ≤ C)
    (hred : IsPReduced 2 (U.subgroupOf C))
    (hmove : ¬ K ≤ centralizer (U : Set G)) : IsFaithfulSignalizerType K := by
  refine ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T hE hlocal, ?_⟩
  intro hz
  have hzero : intrinsicSignalizerModule (K.subgroupOf C) = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    rw [← intrinsicSignalizerModule_map_of_injective C.subtype C.subtype_injective,
      map_subgroupOf_eq_of_le hKC.1, hz]
  have hp : IsPPerfect 2 (K.subgroupOf C) := by
    let := hKC.2.perfect
    intro N hn hN
    let := hn
    let := hN.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hcomm : ⁅U.subgroupOf C, K.subgroupOf C⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono hred.le_reducedPSubgroup le_rfl).trans
      ((reduced_commutator_le_intrinsicModule _ hKC.2.subnormal hp).trans_eq hzero)
  have hc := commutator_eq_bot_iff_le_centralizer.mp hcomm
  apply hmove
  intro k hk u hu
  exact (congrArg Subtype.val (hc
    (show (⟨u,hUC hu⟩ : C) ∈ U.subgroupOf C from hu) ⟨k,hKC.1 hk⟩ hk)).symm

omit [Finite G] in
/-- Relative normality of a common overgroup promotes a C-component.
No normality in the ambient simple group is used. -/
theorem component_in_overgroup {K B J M : Subgroup G}
    (hKJ : (K.subgroupOf J).IsCComponent)
    (hKB : K ≤ B) (hBJ : B ≤ J) (hBM : B ≤ M)
    (hMB : M ≤ normalizer (B : Set G)) :
    (K.subgroupOf M).IsCComponent := by
  have hKBcomp := hKJ.subgroupOf_of_le hKB hBJ
  let := normal_subgroupOf_of_le_normalizer hMB
  have hcomp : ((K.subgroupOf M).subgroupOf (B.subgroupOf M)).IsCComponent := by
    have he : (K.subgroupOf B).map (subgroupOfEquivOfLe hBM).symm.toMonoidHom =
        (K.subgroupOf M).subgroupOf (B.subgroupOf M) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact hy
      · intro hx; exact ⟨⟨x,hKB hx⟩,hx,rfl⟩
    exact he ▸ hKBcomp.map_equiv (subgroupOfEquivOfLe hBM).symm
  have hm := hcomp.map_subtype (inferInstance : (B.subgroupOf M).Normal).isSubnormal
  simpa only [map_subgroupOf_eq_of_le (show K.subgroupOf M ≤ B.subgroupOf M from
    comap_mono hKB)] using hm

/-- Overgroup invariance of the literal Sylow orbit rules out a larger
member of L(G,T), by minimality of C-components in a common overgroup. -/
theorem maximal_of_orbit_normalizers {K J : Subgroup G}
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : K ∈ Chapter1.cComponentsIn J)
    (hJ : J = componentOrbit K (T : Subgroup G) ⊔ (T : Subgroup G))
    (hcontrol : ∀ M : Subgroup G, IsMaximalTwoLocal M → J ≤ M →
      M ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G)) :
    K ∈ Chapter1.LStar G (T : Subgroup G) := by
  refine ⟨hlocal, ?_⟩
  intro R hR hKR
  have hc : pCore 2 (R ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
    intro he
    apply hR.2.2
    change (pCore 2 (R ⊔ (T : Subgroup G) : Subgroup G)).map _ = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨M,hM,hRM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (R ⊔ (T : Subgroup G)) hc
  have hJM : J ≤ M := by
    rw [hJ, componentOrbit_sup]
    exact (sup_le_sup_right hKR _).trans hRM
  have hKM := component_in_overgroup hKJ.2 (le_componentOrbit K T)
    (hJ ▸ le_sup_left) (le_sup_left.trans (hJ ▸ hJM)) (hcontrol M hM hJM)
  have hKRT := hKM.subgroupOf_of_le (hKR.trans le_sup_left) hRM
  have he := hKRT.eq_of_le hR.1 (comap_mono hKR)
  have hg := congrArg (map (R ⊔ (T : Subgroup G)).subtype) he
  simpa only [map_subgroupOf_eq_of_le (hKR.trans le_sup_left),
    map_subgroupOf_eq_of_le (show R ≤ R ⊔ (T : Subgroup G) from le_sup_left)] using hg.symm

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
