module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.TwoConjugates
/-!
# Baumann's argument for two conjugate Thompson subgroups

If the module centralizer is the ambient two-core and lies in R, the
structural and Frattini hypotheses of B.2.18 follow. Two residual conjugates
of J(R), generating the action with the required fixed-codimension bound,
then give the alpha decomposition. The centralizer Sylow conclusion becomes
an equality because the whole module centralizer is a two-group.
Unlike the minimal-parabolic specialization, R need not be Sylow.
Source: Aschbacher–Smith B.2.18, pp.80–81, as used in C.1.37, p.143.
The original unitary application is OriginalUnitaryBaumann.CoreAction.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB.BaumannArgument
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

theorem two_conjugate_hypotheses_of_core_kernel
    (R : Subgroup G) (hR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUT : U ≤ R) (hC : centralizer (U : Set G) = pCore 2 G)
    (q : G →* D) (hker : q.ker = centralizer (U : Set G))
    (hno : NoStrongOffenders U R)
    (g : G) (hg : g ∈ pResidual 2 G)
    (hgen : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ R).map q ⊔
      ((elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom).map q)
    (hcod : 2 * fixedCodim U (elementaryAbelianMaxJ R) ≤
      fixedCodim U (pResidual 2 G)) :
    HypothesesAD U R (fun b : Bool => if b then
      (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom
      else elementaryAbelianMaxJ R) := by
  let J := elementaryAbelianMaxJ R
  let Jg := J.map (MulAut.conj g).toMonoidHom
  have hJT : J ≤ R := sSup_le fun _ hA => hA.1
  have hCQ : R ⊓ centralizer (U : Set G) = pCore 2 G := by
    rw [hC, inf_eq_right.mpr (hQR)]
  have hcore : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩
  have hfr : pResidual 2 G ⊓ centralizer (U : Set G) ≤ coreFrattini (pResidual 2 G) := by
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
  refine { R_two := hR
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
  · change pResidual 2 G ≤ normalizer ((R ⊓ centralizer (U : Set G) : Subgroup G) : Set G)
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



/-- Two equal-cost residual conjugates give the alpha decomposition and saturate
 the centralizer of the module in the residual--Baumann product. -/
theorem two_conjugate_baumann_of_core_kernel
    (R : Subgroup G) (hR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (hC : centralizer (U : Set G) = pCore 2 G)
    (q : G →* D) (hker : q.ker = centralizer (U : Set G))
    (hno : NoStrongOffenders U R)
    (g : G) (hg : g ∈ pResidual 2 G)
    (hgen : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ R).map q ⊔
      ((elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom).map q)
    (hcod : 2 * fixedCodim U (elementaryAbelianMaxJ R) ≤ fixedCodim U (pResidual 2 G)) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann R ∧
      thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (U ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      baumann R ⊓ centralizer (U : Set G) =
        (pResidual 2 G ⊔ baumann R) ⊓ centralizer (U : Set G) := by
  let X : Bool → Subgroup G := fun b => if b then
    (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom else elementaryAbelianMaxJ R
  have hh := two_conjugate_hypotheses_of_core_kernel R hR hQR U hUR hC q hker hno g hg hgen hcod
  have hc := ChapterB.lemma_B_2_18 U R X hh (le_iSup_of_le false le_rfl)
  have hQ : IsSylowSubgroupIn (R ⊓ centralizer (U : Set G))
      ((pResidual 2 G ⊔ R) ⊓ centralizer (U : Set G)) := by
    rw [hC,inf_eq_right.mpr hQR,inf_eq_right.mpr (hQR.trans le_sup_right)]
    obtain ⟨S,hS⟩ := (pCore_isPGroup (p := 2) (G := G)).to_subgroup (⊤ : Subgroup (pCore 2 G)) |>.exists_le_sylow
    refine ⟨S,?_⟩
    have ht : (S : Subgroup (pCore 2 G)) = ⊤ := top_unique hS
    simp only [ht,←MonoidHom.range_eq_map,range_subtype]
  have hs := (hc.2.2 hQ).1
  obtain ⟨S,hS⟩ := hs
  have hp : IsPGroup 2 ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (U : Set G) : Subgroup G) :=
    (hC.symm ▸ pCore_isPGroup).to_le inf_le_right
  have ht : (S : Subgroup ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (U : Set G) : Subgroup G)) = ⊤ :=
    (S.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  refine ⟨hc.1,hc.2.1,?_⟩
  simpa only [ht,←MonoidHom.range_eq_map,range_subtype] using hS.symm

end CFSG.Quasithin.ChapterB.BaumannArgument
