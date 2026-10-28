module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.PrimeSharp.Actors
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.PrimeLinearUniform

/-!
# Sharp generation for the actual paired prime-field PSL₂ source

Core-free minimality makes the two-residual a genuine chief subgroup. The
original generating component lies in that residual and gives its nonabelian
component. For each elementary family whose generation target were proper,
the weak-closure normalizer forces an original actor noncentral on the factor.
Its literal stabilizer-action image has order at most two or exactly four.
The first case supplies an actual degree-one member; the second uses the
proved same-actor prime-field odd escape, including p=7 and outer actors.
Thus every family generates at degree one. Source: Aschbacher–Smith E.1.11
and the paired prime row in E.2.2, printed pp.213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.PrimeSharp
variable {G : Type*} [Group G] [Finite G]

theorem source_residual_chief (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hKR : K ≤ pResidual 2 G) : ChiefFactor.IsChief (pResidual 2 G) ⊥ := by
  let := hK.2
  have hKn : K ≠ ⊥ := by
    intro he
    have : Subsingleton K := he ▸ inferInstance
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  refine ⟨inferInstance,inferInstance,bot_lt_iff_ne_bot.mpr (fun h => hKn (bot_unique (h ▸ hKR))),?_⟩
  intro N hN _ hNR
  let := hN
  rcases ChapterB.minimalParabolic_normal_subgroup_residual_dichotomy T hP N with h | h
  · exact .inl (bot_unique (hJ ▸ h))
  · exact .inr (le_antisymm hNR h)

theorem coreFree_prime_linear_isEGenerated_one
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hm : ClassicalGroup.IsPSL K 2 p) :
    IsEGenerated 1 G := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have hcore := SimpleSocle.pCore_eq_bot hrad 2
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup K := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hK.1
  have hKR : K ≤ pResidual 2 G := (le_componentOrbit K (T : Subgroup G)).trans_eq
    (generating_component_orbit_eq_residual hG T hK hgen)
  have hX := source_residual_chief T hP hJ hK hKR
  have hna : ¬IsMulCommutative (pResidual 2 G) := by
    intro hh
    let := hh
    let : CommGroup (pResidual 2 G) := IsMulCommutative.instCommGroup
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_isSolvable_injective
      (f:=inclusion hKR) (inclusion_injective hKR))
  have hKin : IsComponentIn K (pResidual 2 G) := ⟨hKR,hK.subgroupOf hKR⟩
  have hop : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  apply IsEGeneratedAt.isEGenerated (T:=T)
  intro Ω hΩ
  change ChiefOrbit.generationTarget 1 T Ω = ⊤
  by_contra hproper
  let M := ChapterB.minimalParabolicMax T hP
  have hmM := ChapterB.minimalParabolicMax_spec T hP
  have hTT : (T : Subgroup G) ≤ ChiefOrbit.generationTarget 1 T Ω :=
    (Subgroup.le_normalizer.trans
      (ValuesEvenClassical.RankOneUpper.normalizer_le_weakClosure_normalizer (T : Subgroup G) hΩ)).trans le_sup_right
  have hTM : ChiefOrbit.generationTarget 1 T Ω ≤ M :=
    hP.1.le_maximal ⟨hmM.2,hmM.1.covBy_top⟩ hTT (lt_top_iff_ne_top.mpr hproper)
  have hNW : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M :=
    le_sup_right.trans hTM
  have hex : ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
      ¬A ≤ centralizer (K : Set G) := by
    by_contra h
    push Not at h
    have hWC : weakClosure (T : Subgroup G) Ω ≤ centralizer (K : Set G) :=
      sSup_le fun A hA => h A hA.1 hA.2
    have hKM : K ≤ M := (le_centralizer_iff.mp hWC).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNW)
    exact hmM.1.ne_top (top_unique (hgen ▸ sup_le hKM hmM.2))
  obtain ⟨A,hA,hAT,hAC⟩ := hex
  let : IsElementaryAbelian 2 A := hΩ.1 A hA
  rcases prime_action_card_dichotomy (A:=A) T hK (by omega) hm with hc | hc
  · obtain ⟨X,hXm,hXM⟩ := small_action_member_escape hG T hP hs hJ hK hgen hn hAT hAC hc
    apply hXM
    exact (show X ≤ eSubgroup 1 (T : Subgroup G) A from le_sSup hXm).trans
      ((le_iSup (fun C : {C : Subgroup G // C ∈ Ω ∧ C ≤ (T : Subgroup G)} =>
        eSubgroup 1 (T : Subgroup G) C.1) ⟨A,hA,hAT⟩).trans (le_sup_left.trans hTM))
  · exact ChiefOrbit.not_confined_of_prime_stabilizer hG T hP hK hgen hcore hX hna hKin
      hp hop hm hΩ hA hAT hc hTM

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.PrimeSharp
