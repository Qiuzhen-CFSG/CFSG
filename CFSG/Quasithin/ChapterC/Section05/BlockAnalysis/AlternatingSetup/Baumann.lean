module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Thompson
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.ResidualGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.TwoConjugates
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Baumann's argument on the original alternating-five extension

The actual module centralizer is O₂ of the normalized block extension.
This supplies the normality and residual Frattini conditions directly.
Two residual conjugates of J(T) have S₅ images generating the action,
with codimensions two and two. B.2.18 therefore gives the original alpha
decomposition without a minimal-parabolic hypothesis on this extension.

Source: Aschbacher–Smith C.5.4(3), p.155, applying B.2.18, pp.80–81.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ChapterB ChapterB.BaumannArgument BinaryPermutation BinaryPermutation.FiveCentralExtension
open SymmetricFive ChapterB.Offenders
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

private theorem two_conjugate_hypotheses
    (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUT : U ≤ T) (hC : centralizer (U : Set G) = pCore 2 G)
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
  have hCQ : (T : Subgroup G) ⊓ centralizer (U : Set G) = pCore 2 G := by
    rw [hC, inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal T)]
  have hcore : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩
  refine { R_two := T.isPGroup'
           V_le_R := hUT
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
      ChapterB.RankOneBaumann.fixedCodim_conjugate,two_mul] using hcod


theorem source_conclusions
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (hC : centralizer (V : Set G) = pCore 2 G)
    (q : G →* Equiv.Perm (Fin 5)) (hker : q.ker = centralizer (V : Set G))
    (e : V ≃* Multiplicative (core (Fin 5)))
    (he : ∀ (s : G) (u : V),
      (e.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : G) = s * (u : G) * s⁻¹)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hA : alternatingGroup (Fin 5) ≤ q.range) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann (T : Subgroup G) ∧
    thompsonAlpha (T : Subgroup G) =
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∧
    IsSylowSubgroupIn (baumann (T : Subgroup G) ⊓ centralizer (V : Set G))
      ((pResidual 2 G ⊔ baumann (T : Subgroup G)) ⊓ centralizer (V : Set G)) := by
  have hVT : V ≤ T := (show V ≤ centralizer (V : Set G) from le_centralizer V).trans
    (hC.le.trans (pCore_isPGroup.le_sylow_of_normal T))
  have hq := surjective_of_thompson_moves V q hker e he T hVT hJ hA
  obtain ⟨_,a,ha⟩ := thompson_baumann_image V q hker e he T hVT hJ hA
  have hJimage : (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (D 5).map (MulAut.conj a).toMonoidHom :=
    (thompson_baumann_image V q hker e he T hVT hJ hA).1.trans ha
  have hK : (pResidual 2 G).map q = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 q hq,Equiv.Perm.twoResidual_eq_alternating]
  obtain ⟨g,hg,hqg⟩ : ∃ g ∈ pResidual 2 G, q g = a * fiveCycle * a⁻¹ :=
    (hK ▸ conjugate_fiveCycle_even a : _ ∈ (pResidual 2 G).map q)
  have himage : ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q =
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hgen : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q := by
    rw [himage,hJimage,hqg,two_conjugate_four_groups_generate]
    exact le_top
  have hcod : 2 * BaumannArgument.fixedCodim V (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      BaumannArgument.fixedCodim V (pResidual 2 G) := by
    rw [fixedCodim_coordinates V q hker e he,fixedCodim_coordinates V q hker e he,
      hJimage,fixedCodim_map_conj,hK,fixedCodim_alternating,
      Offenders.Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl]
  have hfr : pResidual 2 G ⊓ centralizer (V : Set G) ≤ coreFrattini (pResidual 2 G) := by
    have hPC : (pCore 2 G).subgroupOf (pResidual 2 G) ≤ pCore 2 (pResidual 2 G) :=
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change QuotientGroup.mk' (pCore 2 (pResidual 2 G)) ⟨x,hx⟩ ∈ frattini _
    have hxp : (⟨x,hx⟩ : pResidual 2 G) ∈ pCore 2 (pResidual 2 G) :=
      hPC (show (⟨x,hx⟩ : pResidual 2 G) ∈ (pCore 2 G).subgroupOf (pResidual 2 G) from hC.le hc)
    rw [show QuotientGroup.mk' (pCore 2 (pResidual 2 G)) ⟨x,hx⟩ = 1 from
      (QuotientGroup.eq_one_iff (N := pCore 2 (pResidual 2 G)) _).mpr hxp]
    exact one_mem _
  let X : Bool → Subgroup G := fun b => if b then
    (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom
      else elementaryAbelianMaxJ (T : Subgroup G)
  have hh : HypothesesAD V (T : Subgroup G) X :=
    two_conjugate_hypotheses T V hVT hC q hker hfr
      (noStrong_of_core_coordinates V q hker e he T) g hg hgen hcod
  have hc := lemma_B_2_18 V (T : Subgroup G) X hh (le_iSup_of_le false le_rfl)
  exact ⟨hc.1,hc.2.1,(hc.2.2 (RankOneBaumann.centralizer_sylow T V)).1⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
