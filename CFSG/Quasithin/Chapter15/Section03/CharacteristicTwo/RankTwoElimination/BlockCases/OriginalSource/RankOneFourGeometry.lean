module
public import Theory.GroupTheory.CoprimeCentralizerImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneTorusGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixed
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Kernel
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.CentralProductProjection
/-!
# The actual moving plane in the field-four source case

The odd action image on V makes the Y_L displacement disjoint from its
fixed subgroup. Its projection into the natural Sylow-fixed line therefore
bounds its order by four, even when U(L) has central covering layers.
An explicit cubic coordinate calculation identifies this displacement as
one of the original two planes. The other plane centralizes L, excluding
the second choice of the local hypotheses and proving Y₊=Y.

All support and Sylow premises are discharged in the source consumer from
the original ambient hypotheses. Source: Aschbacher–Smith15.3.18,
printed pp.1126–1127. Residual identification and the final conjugate pair
remain separate consumers of this geometric conclusion.
-/
public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open RankTwo Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem residual_moving_disjoint (d : LocalData G) (A : Subgroup G)
    (hAY : A ≤ d.Y)
    (h7 : d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Disjoint ⁅d.V,A⁆ (d.V ⊓ centralizer (A : Set G)) := by
  have hAM := hAY.trans (Chapter14.SourcePreliminaries.sourceResidual_le _ _)
  have hn := hAM.trans d.action.normalizes
  let : IsMulCommutative d.V := ⟨⟨fun x y => d.action.coordinates.injective (by
    simp only [map_mul,mul_comm])⟩⟩
  apply commutator_disjoint_centralizer_of_actionRange_coprime d.V A hn
  let f := d.V.normalizerMonoidHom.comp (inclusion hn)
  let a := d.action.actor.comp (inclusion hAM)
  have hk : f.ker = a.ker := by
    rw [natural_restricted_actor_ker,←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  have hc : Nat.card f.range ∣ 9 := by
    rw [←index_ker,hk,index_ker,natural_restricted_actor_range]
    rw [←orthogonal_twoResidual_card,←h7]
    exact card_dvd_of_le (map_mono (comap_mono hAY))
  rw [d.action.card_vector]
  exact (by decide : Nat.Coprime 9 16).of_dvd_left hc

/-- The actual moving subgroup of a natural block embeds in its Sylow-fixed
natural line. Its central cover kernel disappears by the odd residual action. -/
theorem natural_moving_card_le
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock c.L n)
    (hRL : d.R ≤ normalizer (c.L : Set G))
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hs : Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R))
    (h7 : d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hU : (ChapterC.blockU c.L).map c.L.subtype = ⁅d.componentSpan c.L,c.L⁆) :
    Nat.card (⁅d.V,YL d c.L⁆ : Subgroup G) ≤ 2^n := by
  let E := ⁅d.V,YL d c.L⁆
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hAY : YL d c.L ≤ d.Y :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      (yplus_le_residualY_of_choice d.choice)
  have hAV : YL d c.L ≤ normalizer (d.V : Set G) :=
    (hAY.trans (Chapter14.SourcePreliminaries.sourceResidual_le _ _)).trans d.action.normalizes
  have hEV : E ≤ d.V := le_normalizer_iff_commutator_le_left.mp hAV
  have hEU : E ≤ (ChapterC.blockU c.L).map c.L.subtype := by
    rw [hU]
    exact commutator_mono (le_conjugateSpanBy _ _) hAL
  have hEL : E ≤ c.L := hEU.trans (map_subtype_le _)
  have hYR : YL d c.L ≤ normalizer (d.R : Set G) :=
    (((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      (le_sup_left : d.Yplus ≤ d.Yplus ⊔ d.S)).trans
      ((d.Yplus ⊔ d.S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (d.Yplus ⊔ d.S) (pCore 2 _)))
  have hER : E ≤ centralizer (d.R : Set G) :=
    (commutator_mono ((V_le_center_R d hR).trans inf_le_right) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (hYR.trans (normalizer_le_normalizer_centralizer d.R)))
  let : (c.L.subgroupOf (c.L ⊔ d.R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le c.L.le_normalizer hRL)
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs
    (show c.L ≤ c.L ⊔ d.R from le_sup_left)
    (inferInstance : (c.L.subgroupOf (c.L ⊔ d.R)).Normal).isSubnormal
  have hE'U : E.subgroupOf c.L ≤ ChapterC.blockU c.L := by
    intro e he
    obtain ⟨u,hu,heq⟩ := hEU he
    exact (Subtype.ext heq : u = e) ▸ hu
  have hE'P : E.subgroupOf c.L ≤ centralizer (P : Set c.L) := by
    intro e he p hp
    exact Subtype.ext ((mem_centralizer_iff.mp (hER he)) p
      ((hP ▸ mem_map_of_mem c.L.subtype hp).1))
  have hdis : Disjoint (E.subgroupOf c.L) (center c.L) := by
    apply disjoint_def.mpr
    intro e he hz
    apply Subtype.ext
    apply disjoint_def.mp (residual_moving_disjoint d (YL d c.L) hAY h7) he
    refine ⟨hEV he,mem_centralizer_iff.mpr ?_⟩
    intro a ha
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨a,hAL ha⟩)
  have hc := hb.card_le_of_sylow_fixed_disjoint_center P (E.subgroupOf c.L) hE'U hE'P hdis
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv] at hc
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory RankTwo
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

theorem natural_fixed_seed_le_centralizer
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock c.L n)
    (hL3 : 3^(Nat.card (YL d c.L)).factorization 3 = 3)
    (hsplit : d.componentSpan c.L = (ChapterC.blockU c.L).map c.L.subtype ⊔
      (d.componentSpan c.L ⊓ centralizer (c.L : Set G))) :
    d.V ⊓ centralizer (YL d c.L : Set G) ≤ centralizer (c.L : Set G) := by
  let U := (ChapterC.blockU c.L).map c.L.subtype
  let C := d.componentSpan c.L ⊓ centralizer (c.L : Set G)
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hUC : U ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (map_subtype_le _)))
  have hAC : C ≤ centralizer (YL d c.L : Set G) :=
    inf_le_right.trans (centralizer_le hAL)
  rintro v ⟨hv,hvA⟩
  have hvUC : v ∈ U ⊔ C := hsplit ▸ le_conjugateSpanBy d.V c.L hv
  have hvprod : v ∈ (U : Set G)*(C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right U C (hUC.trans (Subgroup.centralizer_le_normalizer _))]
    exact hvUC
  obtain ⟨u,hu,z,hz,rfl⟩ := hvprod
  have huA : u ∈ centralizer (YL d c.L : Set G) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (YL d c.L : Set G)).mul_mem hvA
        ((centralizer (YL d c.L : Set G)).inv_mem (hAC hz))
  obtain ⟨l,hl,he⟩ := hu
  change (l:G)=u at he
  have hlA : l ∈ centralizer ((YL d c.L).subgroupOf c.L : Set c.L) := by
    intro a ha
    apply Subtype.ext
    change (a:G)*(l:G)=(l:G)*(a:G)
    rw [he]
    exact (mem_centralizer_iff.mp huA) a ha
  have hA3 : 3^(Nat.card ((YL d c.L).subgroupOf c.L)).factorization 3 = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv]
    exact hL3
  have hlZ := hb.blockU_fixed_le_center_of_three_part ((YL d c.L).subgroupOf c.L) hA3 ⟨hl,hlA⟩
  have huL : u ∈ centralizer (c.L : Set G) := by
    rw [←he]
    intro a ha
    exact congrArg Subtype.val ((mem_center_iff.mp hlZ) ⟨a,ha⟩)
  exact (centralizer (c.L : Set G)).mul_mem huL hz.2
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open RankTwo
variable {G : Type*} [Group G] [Finite G]
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

private theorem residual_actor_cube (a : OrthogonalActor)
    (ha : a ∈ Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) : a^3=1 := by
  rw [orthogonal_twoResidual_eq_pResidual] at ha
  obtain ⟨e⟩ := Theory.GroupTheory.WreathTwoResidual.residual_equiv_elementaryNine
  have hh : (⟨a,ha⟩ : pResidual 2 OrthogonalActor)^3=1 := by
    apply e.injective
    rw [map_pow,map_one]
    exact (show ∀ x : Multiplicative (Fin 2 → ZMod 3), x^3=1 from by decide) _
  exact congrArg Subtype.val hh

private theorem cubic_actor_displacement (a : OrthogonalActor) (ha : a^3=1) (hne : a≠1) :
    ∃ i : OrthogonalPlaneIndex, ∀ w : OrthogonalVector,
      w ∈ orthogonalCoordinatePlane i → ∃ v : OrthogonalVector, a • v * v⁻¹ = w := by
  have hr3 : a.right^3=1 := by
    have he := congrArg (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex) ha
    simpa only [map_pow,map_one,RegularWreathProduct.rightHom_eq_right] using he
  have hr2 : a.right^2=1 := (show ∀ x : OrthogonalPlaneIndex, x^2=1 from by decide) _
  have hr : a.right=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 2 3) (orderOf_dvd_of_pow_eq_one hr2) (orderOf_dvd_of_pow_eq_one hr3))
  have hi : ∃ i, a.left i ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hne (RegularWreathProduct.ext (funext hh) hr)
  obtain ⟨i,hi⟩ := hi
  have hi3 : (a.left i)^3=1 := by
    have he := congrArg (fun b : OrthogonalActor => b.left i) ha
    simpa [pow_succ,hr] using he
  have hm : ∀ (b : OrthogonalPlaneActor), b^3=1 → b≠1 → ∀ w : OrthogonalPlaneVector,
      b • (b • w) * (b • w)⁻¹ = w := by decide +kernel
  refine ⟨i,fun w hw => ?_⟩
  let v : OrthogonalVector := fun j => if j=i then a.left i • w i else 1
  refine ⟨v,?_⟩
  funext j
  change a.left j • v (a.right⁻¹*j) * (v j)⁻¹ = w j
  rw [hr,inv_one,one_mul]
  by_cases hj : j=i
  · subst j
    simpa only [v,if_pos rfl] using hm (a.left i) hi3 hi (w i)
  · simp only [v,if_neg hj,smul_one,inv_one,mul_one,hw j hj]

/-- A nontrivial displacement of order at most four under the original odd
orthogonal actor is one of the actual two definite coordinate planes. -/
theorem residual_small_moving_eq_plane (d : LocalData G) (A : Subgroup G)
    (hAY : A ≤ d.Y)
    (h7 : d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hne : ⁅d.V,A⁆ ≠ ⊥) (hcard : Nat.card (⁅d.V,A⁆ : Subgroup G) ≤ 4) :
    ∃ i : OrthogonalPlaneIndex, ⁅d.V,A⁆ = d.action.plane i := by
  have hAM := hAY.trans (Chapter14.SourcePreliminaries.sourceResidual_le _ _)
  have hIm : d.action.image A ≠ ⊥ := by
    intro he
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro a ha
    let m : d.M := ⟨a,hAM ha⟩
    have hm : d.action.actor m ∈ d.action.image A := mem_map_of_mem _ ha
    rw [he] at hm
    have hk : m ∈ d.action.actor.ker := mem_bot.mp hm
    rw [d.action.ker_actor] at hk
    exact hk
  obtain ⟨a,ha,ha1⟩ := (d.action.image A).bot_or_exists_ne_one.resolve_left hIm
  have ha3 := residual_actor_cube a (h7 ▸ (map_mono (comap_mono hAY) ha))
  obtain ⟨i,hi⟩ := cubic_actor_displacement a ha3 ha1
  have hle : d.action.plane i ≤ ⁅d.V,A⁆ := by
    intro w hw
    obtain ⟨w,hw,rfl⟩ := hw
    obtain ⟨v,hv⟩ := hi (d.action.coordinates w) hw
    obtain ⟨m,hm,rfl⟩ := ha
    let v₀ := d.action.coordinates.symm v
    have hv₀ : ⁅(m : G),(v₀ : G)⁆ = (w : G) := by
      have he : d.V.normalizerMonoidHom ⟨m,d.action.normalizes m.property⟩ v₀ * v₀⁻¹ = w := by
        apply d.action.coordinates.injective
        rw [map_mul,map_inv,d.action.compatible,d.action.coordinates.apply_symm_apply]
        exact hv
      exact congrArg Subtype.val he
    change (w : G) ∈ ⁅d.V,A⁆
    rw [←hv₀,commutator_comm]
    exact commutator_mem_commutator hm v₀.property
  exact ⟨i,(eq_of_le_of_card_ge hle (by rwa [d.action.card_plane])).symm⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource


namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup RankTwo Theory.GroupTheory ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The field-four source case has a genuine moving coordinate plane, and
its complementary coordinate plane centralizes the selected component.
This also forces the first choice Y₊=Y of the original local hypotheses. -/
theorem naturalFour_source_plane_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hb : ChapterC.IsL2EvenBlock c.L 2) :
    d.Yplus = d.Y ∧ ∃ i j : OrthogonalPlaneIndex, i ≠ j ∧
      ⁅d.V,YL d c.L⁆ = d.action.plane i ∧
      d.action.plane j ≤ centralizer (c.L : Set G) := by
  obtain ⟨hSyl,_,_,_,hL3,_⟩ :=
    naturalFour_source_local_geometry hG d hempty hM hu hmany hI htwo c hb
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hC : centralizer (d.V : Set G) ≤ d.M :=
    (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hW := RankTwoElimination.OriginalSource.source_lemma_15_3_16_span_isR2
    hG d hempty hM hu hmany hI htwo hf c
  have hWL : d.componentSpan c.L ≤ c.L ⊔ d.R :=
    conjugateSpanBy_le ((V_le_R d htwo.2.2.2.2.1).trans le_sup_right)
      (le_sup_left.trans (c.L ⊔ d.R).le_normalizer)
  have hU := natural_block_support d c h.normalizes hW hWL hC hb.2.1
  have hsplit := natural_block_span_split d c h.normalizes htwo.2.2.2.2.1 hSyl hb.2.1 hU
  have hfix := natural_fixed_seed_le_centralizer d c hb hL3 hsplit
  have hne : ⁅d.V,YL d c.L⁆ ≠ ⊥ := by
    intro he
    have hh : d.V ≤ centralizer (c.L : Set G) :=
      (le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.mp he)).trans hfix
    exact c.outside ((le_centralizer_iff.mp hh).trans hC)
  obtain ⟨hne',_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne').1
  have hcard : Nat.card (⁅d.V,YL d c.L⁆ : Subgroup G) ≤ 4 :=
    natural_moving_card_le d c hb h.normalizes htwo.2.2.2.2.1 hSyl h7 hU
  have hAY : YL d c.L ≤ d.Y :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      (yplus_le_residualY_of_choice d.choice)
  obtain ⟨i,hi⟩ := residual_small_moving_eq_plane d (YL d c.L) hAY h7 hne hcard
  let j : OrthogonalPlaneIndex := i * Multiplicative.ofAdd (1 : ZMod 2)
  have hij : i ≠ j := (show ∀ i : OrthogonalPlaneIndex,
      i ≠ i * Multiplicative.ofAdd (1 : ZMod 2) from by decide) i
  have hAj : YL d c.L ≤ normalizer (d.action.plane j : Set G) :=
    perfect_normalizes_planes d.action
      (hAY.trans (Chapter14.SourcePreliminaries.sourceResidual_le _ _))
      (ComponentIntersection.intersectionResidual_isPPerfect _ _) j
  have hjA : d.action.plane j ≤ centralizer (YL d c.L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (le_inf ((commutator_mono (d.action.plane_le j) le_rfl).trans hi.le)
      (le_normalizer_iff_commutator_le_left.mp hAj)).trans
      (natural_planes_disjoint d.action hij).le_bot
  have hjL : d.action.plane j ≤ centralizer (c.L : Set G) :=
    (le_inf (d.action.plane_le j) hjA).trans hfix
  have hfirst : d.Yplus = d.Y := by
    rcases d.choice with hfirst | hsecond
    · exact hfirst
    · have hs := (OutsideStructure.source_lemma_15_3_11_from_selection
        hG d hempty hM hu hmany I hI).second_choice hsecond
      have hbound : normalizer (d.action.plane j : Set G) ≤ d.M := by
        have hj : j=1 ∨ j=Multiplicative.ofAdd (1 : ZMod 2) := by
          exact (show ∀ j : OrthogonalPlaneIndex,
            j=1 ∨ j=Multiplicative.ofAdd (1 : ZMod 2) from by decide) j
        rcases hj with hj | hj
        · simpa only [hj] using hs.2.1
        · simpa only [hj] using hs.2.2.1
      exact (c.outside (((le_centralizer_iff.mp hjL).trans
        (Subgroup.centralizer_le_normalizer _)).trans hbound)).elim
  exact ⟨hfirst,i,j,hij,hi,hjL⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
