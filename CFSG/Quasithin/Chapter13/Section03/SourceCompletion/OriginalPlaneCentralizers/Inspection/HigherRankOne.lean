module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.FieldParity
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelResidual
public import Theory.GroupTheory.PResidual.ThreeFree
public import Theory.GroupTheory.PResidual.PrimeSetSubgroupMaps

/-!
# Excluding every rank-one field on the original plane component

The {2,3}-residual of the actual local plane centralizer acts trivially on
V, since its faithful plane-action quotient has order dividing six. In a
higher-field natural rank-one block, the Borel residual fixes only central
vectors of U(J). The original perpendicular sixteen-group lies in U(J):
use its centrality in Q, the selected Sylow placement in JQ, characteristic
two, and the actual marked cubic. Thus the Borel residual would make that
sixteen-group central in J, contradicting the cubic commutator identity.
The already proved L₂(4) endpoint handles the smallest field.

The final application retains the full moved section on the same component
and plane, leaving precisely the two odd-degree linear-three action rows.
It does not assert their residual identification, binary MS hypotheses, or
chief-factor exclusion; these remain with the original-plane assembly.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890. The higher-field
step uses the natural Borel residual calculation also used in 13.6.18.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The literal {2,3}-residual of C_M(A) fixes the chosen module. -/
theorem Context.plane_piResidual_centralizes (s : Context T L V) (d : MarkedPlane V) :
    (piResidual twoThreePrimes (centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G)).map
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).subtype ≤
        centralizer (V : Set G) := by
  let f := s.planeCentralizerAction d
  have hp : IsPiGroup twoThreePrimes
      ((centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G) ⧸ f.ker) := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hp
    have hd := hp.trans (s.planeCentralizerAction_quotient_card_dvd_six d)
    rcases p.property.dvd_mul.mp (show p.val ∣ 2 * 3 from hd) with h | h
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left p.property.ne_one)
  have hr : piResidual twoThreePrimes _ ≤ f.ker := sInf_le ⟨inferInstance,hp⟩
  rintro _ ⟨x,hx,rfl⟩
  have hx' := hr hx
  rw [s.planeCentralizerAction_ker d] at hx'
  exact hx'

/-- Sylow placement and the marked cubic put the perpendicular E₁₆ in U(J). -/
theorem Context.perpendicular_le_blockU_of_sylow (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (hQ : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2)) :
    perpendicular d.coordinates ≤ (ChapterC.blockU J).map J.subtype := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  obtain ⟨n,hnJ,hn⟩ := s.component_marked_cubic d J j
  have hEQ := chosen_perpendicular_central s d.coordinates
  have hEQ' : perpendicular d.coordinates ≤ Q := hEQ.trans (map_subtype_le _)
  have hEC : perpendicular d.coordinates ≤ centralizer (Q : Set G) := by
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hEQ hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y,hy⟩)
  have hm := perpendicular_commutator d.chart d.coordinates d.equivariant n hn
  have hEJ : perpendicular d.coordinates ≤ J := by
    rw [←hm,commutator_comm]
    exact (commutator_mono le_rfl (zpowers_le.mpr hnJ)).trans
      (le_normalizer_iff_commutator_le_right.mp (hEQ'.trans j.input.normalizes))
  obtain ⟨S,hS⟩ := hQ
  have hcoreQ : D.pCoreIn 2 ≤ Q := by
    change (S : Subgroup D).map D.subtype = Q at hS
    exact (pCoreIn_le_sylow D S).trans hS.le
  have hchar : HasCharacteristicTwo D := by
    have hc := ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := D)
    rwa [ChapterC.C27Source.source_join_fitting j.input] at hc
  have hEcore : perpendicular d.coordinates ≤ D.pCoreIn 2 := by
    intro x hx
    refine ⟨⟨x,mem_sup_right (hEQ' hx)⟩,hchar ?_,rfl⟩
    intro y hy
    exact Subtype.ext (hEC hx y.val (hcoreQ (mem_map_of_mem D.subtype hy)))
  have hEcoreJ : perpendicular d.coordinates ≤ J.pCoreIn 2 :=
    (le_inf hEJ hEcore).trans (inf_pCoreIn_le_of_le 2 (show J ≤ D from le_sup_left))
  rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype,
    ←hm,commutator_comm]
  exact commutator_mono hEcoreJ (zpowers_le.mpr hnJ)

private theorem rankOne_borel_model (d : MarkedPlane V) (J : Subgroup G)
    (j : LocalData T L d J) {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (J ⧸ pCore 2 J) ≃* SL(2,F))
    (hb : IsRankOneBorel (starImage J ((L ⊔ T).pCoreIn 2) J)
      (starM J ((L ⊔ T).pCoreIn 2) (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)))) :
    ∃ P : Sylow 2 SL(2,F),
      ((centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).subgroupOf J).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))) = normalizer (P : Set SL(2,F)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let C := starImage J Q J
  let B := M.subgroupOf J
  have hz : center (J ⧸ pCore 2 J) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    have he : e x = 1 := (Theory.PSL2.sl2_center_eq_bot F).le hh
    exact e.map_eq_one_iff.mp he
  let f := coreToStar j.input.normalizes
  have hk : f.ker = ⊥ := bot_unique
    ((ChapterC.C27Source.coreToStar_ker_central_from_source j.input).trans hz.le)
  let ce := MulEquiv.ofBijective f ⟨f.ker_eq_bot_iff.mp hk,coreToStar_surjective j.input.normalizes⟩
  let a : C ≃* SL(2,F) := ce.symm.trans e
  obtain ⟨S,hS⟩ := hb
  let P := S.mapSurjective (f := a.toMonoidHom) a.surjective
  refine ⟨P,?_⟩
  have hm : B.map (toStarImage J Q) = (starM J Q M).subgroupOf C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,mem_sup_left x.property⟩,⟨hx,x.property⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,he⟩ := hy
      exact ⟨⟨x.val,hx.2⟩,hx.1,Subtype.ext he⟩
  have hcomp : a.toMonoidHom.comp (toStarImage J Q) =
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J)) := by
    apply MonoidHom.ext
    intro x
    change e (ce.symm (ce (QuotientGroup.mk' (pCore 2 J) x))) =
      e (QuotientGroup.mk' (pCore 2 J) x)
    rw [ce.symm_apply_apply]
  change B.map _ = _
  rw [←hcomp,←map_map,hm]
  rw [hS]
  change ((normalizer (S : Set C)).map C.subtype |>.comap C.subtype).map a.toMonoidHom = _
  rw [comap_map_eq_self_of_injective C.subtype_injective]
  exact map_equiv_normalizer_eq (S : Subgroup C) a

/-- No natural rank-one block survives with its actual Borel and Sylow marking. -/
theorem Context.not_rankOne_borel (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (hs : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2))
    (hM : IsRankOneBorel (starImage J ((L ⊔ T).pCoreIn 2) J)
      (starM J ((L ⊔ T).pCoreIn 2) (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))))
    {m : ℕ} (hb : ChapterC.IsL2EvenBlock J m) : False := by
  by_cases hm : m ≤ 2
  · have he : m = 2 := by have := hb.1; omega
    exact s.not_four_block d J j hs (he ▸ hb)
  have hm : 2 < m := by omega
  obtain ⟨_,_,F,_,_,hF,_,r,⟨b⟩,hr⟩ := hb
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let B := M.subgroupOf J
  let N := (piResidual twoThreePrimes B).map B.subtype
  have hNC : N.map J.subtype ≤ centralizer (V : Set G) :=
    (map_embedded_piResidual_le twoThreePrimes B M J.subtype
      (by rw [subgroupOf_map_subtype]; exact inf_le_left)).trans
        (s.plane_piResidual_centralizes d)
  obtain ⟨P,hP⟩ := rankOne_borel_model d J j b.quotientIso hM
  have hfix := ChapterC.natural_block_residual_fixed_le_center hm hF r b hr B P hP
  have hEU := s.perpendicular_le_blockU_of_sylow d J j hs
  have hEJ : perpendicular d.coordinates ≤ J := hEU.trans (map_subtype_le _)
  have hEZ : perpendicular d.coordinates ≤ (center J).map J.subtype := by
    intro x hx
    let xJ : J := ⟨x,hEJ hx⟩
    have hxU : xJ ∈ ChapterC.blockU J := by
      obtain ⟨y,hy,he⟩ := hEU hx
      exact (show y = xJ from Subtype.ext he) ▸ hy
    refine ⟨xJ,hfix ⟨hxU,?_⟩,rfl⟩
    intro y hy
    exact Subtype.ext ((hNC (mem_map_of_mem J.subtype hy)) x (perpendicular_le _ hx)).symm
  have hEC : perpendicular d.coordinates ≤ centralizer (J : Set G) := by
    rintro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hEZ hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y,hy⟩)
  obtain ⟨n,hnJ,hn⟩ := s.component_marked_cubic d J j
  have hbot : perpendicular d.coordinates = ⊥ := by
    rw [←perpendicular_commutator d.chart d.coordinates d.equivariant n hn,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hEC.trans (centralizer_le (zpowers_le.mpr hnJ)))
  have hc := perpendicular_card d.coordinates
  rw [hbot,Subgroup.card_bot] at hc
  norm_num at hc

/-- The full original moved section has one of the two odd-degree SL₃ actions. -/
theorem Context.odd_linearThree_moved_section (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K, PlaneOddLinearThreeCase (ρ.comp B.subtype) K c.sectionData := by
  rcases s.even_block_or_odd_higher_action d J j with ⟨hs,hM,m,hb⟩ | ⟨c,hc⟩
  · exact (s.not_rankOne_borel d J j hs hM hb).elim
  cases hc with
  | linearThree F ho a => exact ⟨c,.natural F ho a⟩
  | doubleThree F ho a => exact ⟨c,.double F ho a⟩
  | symmetricFive a =>
    obtain ⟨hK,_⟩ := ChapterC.C27Source.star_moved_section_from_source j.input
    exact (s.not_alternatingFive_star d J j
      ((subgroupOfEquivOfLe hK).symm.trans a.subgroupEquiv)).elim

/-- Apply the field exclusion to the component extracted from the escaping
centralizer of this same plane. -/
theorem Context.exists_odd_linearThree_moved_section (s : Context T L V)
    (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G, Nonempty (LocalData T L d J) ∧
      let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
      let B := offenderSubgroup ρ
      let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) K, PlaneOddLinearThreeCase (ρ.comp B.subtype) K c.sectionData := by
  obtain ⟨J,⟨j⟩⟩ := s.localExtraction d hout
  exact ⟨J,⟨j⟩,s.odd_linearThree_moved_section d J j⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
