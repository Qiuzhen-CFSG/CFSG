module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Frattini
public import CFSG.Quasithin.ChapterB.Section02.Baumann
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The two-conjugate application of Baumann's argument

For the original minimal parabolic and reduced normal elementary subgroup,
movement identifies the Sylow centralizer with O₂. Two actual residual
conjugates of J(T), their action-image generation, and their fixed-space
codimensions supply the remaining geometric clauses of B.2.18. Its source
conclusions give the alpha decomposition and the two-core and centralizer
Sylow containments needed by both the natural SL₂ and S₅ branches.
The individual model owners supply generation, dimensions, absence of strong
offenders, and the genuine Frattini containment through their actual maps.
Source: Aschbacher–Smith B.2.18 and B.6.10, printed pp.81 and117.
-/

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G D : Type*} [Group G] [Finite G] [Group D]

private theorem maxJ_self_rank (R : Subgroup G) :
    elementaryAbelianMaxJ (elementaryAbelianMaxJ R) = elementaryAbelianMaxJ R ∧
      twoRank (elementaryAbelianMaxJ R) = twoRank R := by
  let J := elementaryAbelianMaxJ R
  have hJR : J ≤ R := sSup_le fun A hA => hA.1
  have hr : twoRank J = twoRank R := twoRank_eq_of_intermediate R J le_rfl hJR
  have ho : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder J :=
    le_antisymm (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R J le_rfl).1
      (elementaryAbelianMaxOrder_le_and_j_le_of_eq J R hJR).1
  exact ⟨le_antisymm (sSup_le fun A hA => hA.1)
    ((elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R J le_rfl).2 ho),hr⟩

omit [Finite G] in
public theorem fixedCodim_conjugate (U A : Subgroup G) [U.Normal] (g : G) :
    fixedCodim U (A.map (MulAut.conj g).toMonoidHom) = fixedCodim U A := by
  have hm : (U ⊓ centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom =
      U ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    have hu : U.map (MulAut.conj g).toMonoidHom = U := Normal.map_conj_eq U g
    rw [hu]
    rw [map_centralizer_equiv]
    rfl
  unfold fixedCodim
  rw [←hm,card_map_of_injective (MulAut.conj g).injective]

public theorem reduced_centralizer_eq_twoCore
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) = pCore 2 G := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hk : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [QuotientGroup.ker_mk'] at he
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ C
    rw [he]
    exact le_top
  have hc : C ≤ minimalParabolicCore T hP := by
    have hh := (minimalParabolic_reduced_image T hP q
      (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hk).1
    simpa only [q,QuotientGroup.ker_mk'] using hh
  exact le_antisymm
    ((inf_le_inf_left _ hc).trans (minimalParabolic_sylow_inf_core T hP).le)
    (le_inf (pCore_isPGroup.le_sylow_of_normal T)
      (le_centralizer_iff.mp hU.le_centralizer_pCore))

public theorem two_conjugate_hypotheses
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hker : q.ker = centralizer (U : Set G))
    (hfr : pResidual 2 G ⊓ centralizer (U : Set G) ≤ coreFrattini (pResidual 2 G))
    (hno : NoStrongOffenders U (T : Subgroup G))
    (g : G) (hg : g ∈ pResidual 2 G)
    (hgen : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q)
    (hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G)) :
    HypothesesAD U (T : Subgroup G) (fun b : Bool => if b then
      (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom
      else elementaryAbelianMaxJ (T : Subgroup G)) := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let Jg := J.map (MulAut.conj g).toMonoidHom
  have hJT : J ≤ T := sSup_le fun _ hA => hA.1
  have hCQ := reduced_centralizer_eq_twoCore T hP U hU hJ
  have hcore : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩
  refine { R_two := T.isPGroup'
           V_le_R := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
           core_le := hCQ.symm ▸ hcore
           normalizes := ?_
           centralizer_le_frattini := hfr
           no_strong := hno
           conjugate_into := ?_
           self_thompson := ?_
           rank_eq := ?_
           image_generation := ?_
           codimension_sum := ?_ }
  · change pResidual 2 G ≤ normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G)
    rw [hCQ]
    exact le_normalizer_of_normal
  · intro b
    cases b
    · refine ⟨1,one_mem _,?_⟩
      rintro _ ⟨j,hj,rfl⟩
      simpa only [Bool.false_eq_true,if_false,MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply,one_mul,inv_one,mul_one] using hJT hj
    · refine ⟨g⁻¹,(pResidual 2 G).inv_mem hg,?_⟩
      change Jg.map (MulAut.conj g⁻¹).toMonoidHom ≤ _
      have he : Jg.map (MulAut.conj g⁻¹).toMonoidHom = J := by
        rw [show Jg = J.map (MulAut.conj g).toMonoidHom from rfl,map_map]
        have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
          ext x
          simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
            MonoidHom.id_apply,inv_inv]
          group
        rw [hh,map_id]
      exact he.le.trans hJT
  · intro b
    cases b
    · exact (maxJ_self_rank _).1
    · exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj g) J).trans
        (congrArg (map (MulAut.conj g).toMonoidHom) (maxJ_self_rank _).1)
  · intro b
    cases b
    · exact (maxJ_self_rank _).2
    · exact (twoRank_map_equiv (MulAut.conj g) J).trans (maxJ_self_rank _).2
  · simp only [iSup_bool_eq,Bool.false_eq_true,if_false,if_true]
    rw [sup_comm,←Subgroup.map_sup]
    apply map_le_iff_le_comap.mpr
    rw [comap_map_eq,actionMap_ker]
    rw [←Subgroup.map_sup,map_le_iff_le_comap,comap_map_eq,hker] at hgen
    exact hgen
  · simpa only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true,
      fixedCodim_conjugate,two_mul] using hcod

public theorem centralizer_sylow
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] :
    IsSylowSubgroupIn ((T : Subgroup G) ⊓ centralizer (U : Set G))
      ((pResidual 2 G ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G)) := by
  rw [pResidual_sup_sylow_eq_top,top_inf_eq]
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal (centralizer (U : Set G))
  refine ⟨S,?_⟩
  rw [hS]
  ext x
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨hc,c.property⟩
  · rintro ⟨ht,hc⟩
    exact ⟨⟨x,hc⟩,ht,rfl⟩
public theorem two_conjugate_alpha_and_saturation
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hker : q.ker = centralizer (U : Set G))
    (hfr : pResidual 2 G ⊓ centralizer (U : Set G) ≤ coreFrattini (pResidual 2 G))
    (hno : NoStrongOffenders U (T : Subgroup G))
    (g : G) (hg : g ∈ pResidual 2 G)
    (hgen : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q)
    (hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G)) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann (T : Subgroup G) ∧
      thompsonAlpha (T : Subgroup G) =
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∧
      IsSylowSubgroupIn (baumann (T : Subgroup G) ⊓ centralizer (U : Set G))
        ((pResidual 2 G ⊔ baumann (T : Subgroup G)) ⊓ centralizer (U : Set G)) := by
  let X : Bool → Subgroup G := fun b => if b then
    (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom
    else elementaryAbelianMaxJ (T : Subgroup G)
  have hh : HypothesesAD U (T : Subgroup G) X :=
    two_conjugate_hypotheses T hP U hU hJ q hker hfr hno g hg hgen hcod
  have hJI : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⨆ b, X b :=
    le_iSup_of_le false le_rfl
  have hc := lemma_B_2_18 U (T : Subgroup G) X hh hJI
  exact ⟨hc.1,hc.2.1,(hc.2.2 (centralizer_sylow T U)).1⟩
end CFSG.Quasithin.ChapterB.RankOneBaumann
