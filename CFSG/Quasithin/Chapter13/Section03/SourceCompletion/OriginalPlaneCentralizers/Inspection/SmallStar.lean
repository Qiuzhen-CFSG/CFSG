module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Normality
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarSylow
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.EvenLinear
public import Theory.SpecificGroups.SymmetricFive.SylowNormalIntersection
public import Theory.SpecificGroups.SL2.RadicalSubgroups
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.QuotientCardSixty
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Full-Sylow inspection of the original A₅ star component

Restrict the selected Sylow subgroup of C_G(A) to the normal component
and its join with Q. The resulting full Sylow normalizes Q. In the star
quotient, a faithful marked S₅ embedding forces Q* to meet the A₅ component.
The nontrivial radical intersection is Sylow in SL₂(4), and the original
central-kernel comparison lifts this to Q Sylow in JQ. The deleted A₅
block is impossible by the module-centralizer cubic obstruction. The
remaining natural block has actual core quotient of order sixty and hence
field size four.

Applying this to the full C.2.7 moved section leaves only natural even-field
blocks or the two odd-degree linear-three markings. The last theorem
extracts and inspects the escaping component of the original plane
centralizer. The residual, general field reductions and chief-factor
contradiction remain with the plane-centralizer assembly owner.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890; C.2.7, pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The selected plane Sylow restricts to a full Sylow of JQ normalizing Q. -/
theorem Context.join_sylow_normalizes_radical (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    ∃ P : Sylow 2 (J ⊔ (L ⊔ T).pCoreIn 2 : Subgroup G),
      ((L ⊔ T).pCoreIn 2).subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2) ≤ (P : Subgroup (J ⊔ (L ⊔ T).pCoreIn 2 : Subgroup G)) ∧
      (P : Subgroup (J ⊔ (L ⊔ T).pCoreIn 2 : Subgroup G)) ≤ normalizer
        (((L ⊔ T).pCoreIn 2).subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2) : Set (J ⊔ (L ⊔ T).pCoreIn 2 : Subgroup G)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let H := centralizer (d.A : Set G)
  let D := J ⊔ Q
  let JH := J.subgroupOf H
  let JD := J.subgroupOf D
  obtain ⟨S,hQS,hSM⟩ := s.plane_sylow_in_normalizer d
  let Sg := (S : Subgroup H).map H.subtype
  have hSg : IsPGroup 2 Sg := S.isPGroup'.map _
  have hSH : Sg ≤ H := map_subtype_le _
  have hQM : Sg ≤ H ⊓ normalizer (L : Set G) := le_inf hSH hSM
  have hQC := (s.plane_twoGroup_index d Sg hSg hQS hQM).1
  change Sg ⊓ centralizer (V : Set G) = Q at hQC
  have hQN : Sg ≤ normalizer (Q : Set G) := by
    rw [←hQC]
    apply le_normalizer_iff.mpr
    intro a ha x hx
    refine ⟨Sg.mul_mem (Sg.mul_mem ha hx.1) (Sg.inv_mem ha),?_⟩
    exact ((normalizer_le_normalizer_centralizer V
      ((s.plane_local_control d).2.2.2 (hQM ha))) x).mp hx.2
  let : JH.Normal := s.local_component_normal d J j
  obtain ⟨S0,hS0⟩ := S.exists_subgroupOf_eq_of_normal JH
  let e : JH ≃* JD := (subgroupOfEquivOfLe j.input.component.1).trans
    (subgroupOfEquivOfLe (show J ≤ D from le_sup_left)).symm
  let SD : Sylow 2 JD := S0.mapSurjective (f := e.toMonoidHom) e.surjective
  let R := Sg.subgroupOf D
  let : JD.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le J.le_normalizer j.input.normalizes)
  have hSR : (SD : Subgroup JD).map JD.subtype ≤ R := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    have hyS : y.val ∈ (S : Subgroup H) := by
      change y ∈ (S : Subgroup H).subgroupOf JH
      rwa [←hS0]
    exact mem_map_of_mem H.subtype hyS
  have hgen : JD ⊔ R = ⊤ := by
    apply top_unique
    rw [←subgroupOf_self D]
    change (J ⊔ Q).subgroupOf D ≤ JD ⊔ R
    rw [subgroupOf_sup (show J ≤ D from le_sup_left) (show Q ≤ D from le_sup_right)]
    exact sup_le_sup_left (comap_mono hQS) _
  obtain ⟨P,hP⟩ := exists_sylow_eq_of_normal_supplement JD R hSg.comap_subtype hgen SD hSR
  refine ⟨P,?_,?_⟩
  · rw [hP]
    exact comap_mono hQS
  · rw [hP,←subgroupOf_normalizer_eq (show Q ≤ D from le_sup_right)]
    exact comap_mono hQN

private noncomputable def fiveLinearEquiv :
    alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm

/-- The original full Sylow placement forces the radical to be Sylow when
its component star quotient is A₅. -/
theorem Context.radical_sylow_of_alternatingFive_star (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* alternatingGroup (Fin 5)) :
    Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  let C := starImage J Q J
  let U := starImage J Q Q
  let q := QuotientGroup.mk' (starKernel J Q)
  let : (J.subgroupOf (centralizer (d.A : Set G))).Normal := s.local_component_normal d J j
  obtain ⟨P,_,hPN⟩ := s.join_sylow_normalizes_radical d J j
  let Pstar := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hUN : (Pstar : Subgroup (StarQuotient J Q)) ≤ normalizer (U : Set (StarQuotient J Q)) :=
    (map_mono hPN).trans ((Q.subgroupOf D).le_normalizer_map q)
  let : (J.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le J.le_normalizer j.input.normalizes)
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hself : centralizer (C : Set (StarQuotient J Q)) ≤ C := by
    have hfit := (ChapterC.C27Source.star_fitting_quasisimple (ChapterC.C27Source.source_join_input j.input)).1
    change centralizer (starImage J Q J : Set (StarQuotient J Q)) ≤ starImage J Q J
    rw [←hfit]
    exact centralizer_generalizedFitting_le _
  obtain ⟨f,hf,he⟩ :=
    Theory.SpecificGroups.SymmetricFive.SylowNormalIntersection.exists_marked_embedding C e hself
  have hne := Theory.SpecificGroups.SymmetricFive.SylowNormalIntersection.subgroupOf_ne_bot_of_marked_extension
    C e f hf he Pstar U (ChapterC.C27Source.star_radical_ne_bot j.input) hUN
  have hr := ChapterC.C27Source.star_intersection_radical_from_source j.input hne
  let a := e.trans fiveLinearEquiv
  obtain ⟨S,hS⟩ := Matrix.SpecialLinearGroup.radical_eq_sylow
    ((U.subgroupOf C).map a.toMonoidHom) (hr.map_equiv a)
  let S0 := S.mapSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  have hS0 : (S0 : Subgroup C) = U.subgroupOf C := by
    change (S : Subgroup _).map a.symm.toMonoidHom = _
    rw [hS,map_map]
    simp
  have hS0U : (S0 : Subgroup C).map C.subtype ≤ U := by
    rw [hS0,subgroupOf_map_subtype]
    exact inf_le_left
  obtain ⟨P0,hP0⟩ := ChapterC.C27Source.radical_sylow_of_star_component_sylow j.input S0 hS0U
  refine ⟨P0,?_⟩
  rw [hP0,map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)]

/-- The A₅ star alias is an actual natural even-field block on the original
component; the deleted A₅ block is excluded by the original module centralizer. -/
theorem Context.even_block_of_alternatingFive_star (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* alternatingGroup (Fin 5)) :
    Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      ∃ n, ChapterC.IsL2EvenBlock J n := by
  have hs := s.radical_sylow_of_alternatingFive_star d J j e
  rcases ChapterC.C27Source.source_rankOne_blocks_of_sylow j.input hs with hb | hb
  · exact ⟨hs,hb⟩
  · exact (s.not_alternatingFive_block_of_sylow d J j hs hb).elim

/-- The A₅ quotient fixes the natural block parameter to four, through the
actual central covering J/O₂(J) → J*. -/
theorem Context.four_block_of_alternatingFive_star (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* alternatingGroup (Fin 5)) :
    Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      ChapterC.IsL2EvenBlock J 2 := by
  obtain ⟨hs,n,hb⟩ := s.even_block_of_alternatingFive_star d J j e
  refine ⟨hs,hb.four_of_quotient_card ?_⟩
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,_⟩ := hb
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hz : center (J ⧸ pCore 2 J) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr m.quotientIso ⟨x,hx⟩).property
    have heq : m.quotientIso x = 1 := (Theory.PSL2.sl2_center_eq_bot F).le hh
    exact m.quotientIso.map_eq_one_iff.mp heq
  let f := coreToStar j.input.normalizes
  have hk : f.ker = ⊥ := bot_unique
    ((ChapterC.C27Source.coreToStar_ker_central_from_source j.input).trans hz.le)
  let a := MulEquiv.ofBijective f ⟨f.ker_eq_bot_iff.mp hk,
    coreToStar_surjective j.input.normalizes⟩
  rw [Nat.card_congr (a.trans e).toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- Only the two odd-degree linear-three markings remain outside the actual
natural even-field block branch. -/
inductive PlaneOddLinearThreeCase {D : Type*} [Group D] {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (K : Subgroup D) (c : MovedSection ρ K) : Prop
  | natural (F : BinaryField) (odd : Odd F.degree)
      (e : ActionEquiv (c.action.comp K.subtype) (linearNatural F 3))
  | double (F : BinaryField) (odd : Odd F.degree)
      (e : ActionEquiv (c.space.toRepresentation.comp K.subtype)
        (repeated (linearNatural F 3) 2))

/-- Apply the full-Sylow A₅ reduction to the original C.2.7 moved section. -/
theorem Context.even_block_or_odd_linearThree (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      ∃ n, ChapterC.IsL2EvenBlock J n) ∨
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K, PlaneOddLinearThreeCase (ρ.comp B.subtype) K c.sectionData := by
  rcases s.even_block_or_odd_higher_action d J j with ⟨hs,_,hb⟩ | ⟨c,hc⟩
  · exact Or.inl ⟨hs,hb⟩
  cases hc with
  | linearThree F ho a => exact Or.inr ⟨c,.natural F ho a⟩
  | doubleThree F ho a => exact Or.inr ⟨c,.double F ho a⟩
  | symmetricFive a =>
    obtain ⟨hK,_⟩ := ChapterC.C27Source.star_moved_section_from_source j.input
    obtain ⟨hs,hb⟩ := s.four_block_of_alternatingFive_star d J j
      ((subgroupOfEquivOfLe hK).symm.trans a.subgroupEquiv)
    exact Or.inl ⟨hs,2,hb⟩
/-- An escaping original plane centralizer supplies this inspected component,
with its actual block or its full odd-degree linear-three source section. -/
theorem Context.exists_even_block_or_odd_linearThree (s : Context T L V)
    (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G, Nonempty (LocalData T L d J) ∧
      let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
      let B := offenderSubgroup ρ
      let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
      (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
        ∃ n, ChapterC.IsL2EvenBlock J n) ∨
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) K, PlaneOddLinearThreeCase (ρ.comp B.subtype) K c.sectionData := by
  obtain ⟨J,⟨j⟩⟩ := s.localExtraction d hout
  exact ⟨J,⟨j⟩,s.even_block_or_odd_linearThree d J j⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
