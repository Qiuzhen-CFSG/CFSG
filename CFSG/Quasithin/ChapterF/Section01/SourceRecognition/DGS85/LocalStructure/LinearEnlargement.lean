module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import Theory.GroupTheory.AmalgamGraph.SylowEmbedding
public import Theory.GroupTheory.NormalSylowQuotientAction.Local
public import Theory.GroupTheory.PCoreQuotientInnerJoin
public import Theory.SpecificGroups.PSL2.TorusFixedInner
public import GorensteinWalter.PSL2Center

/-!
# Linear model recognition for the actual Chapter 6 enlargement

Let S = O₂(B). The marked starred Sylow is S intersect G*, and its
normalizer preserves S. The induced S-action on G*/O₂(G*) therefore has
trivial displacements on the Sylow normalizer quotient. For a binary PSL₂
model this forces inner action. The inner-action join theorem and the
unchanged embedded core give G*S = G*, including the field of order two.

In the reduced F1.11 application, the intrinsic graph actor embeds onto
the original starred parabolic. Its quotient map is the original local
quotient followed by the proved starred inclusion, with representative
formulas retained. Only local groups are finite; the completion is arbitrary.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, the linear case of 6.1, pp.118--119; Aschbacher--Smith F.1.9,
pp.261--262. The other model alternatives of 6.1 remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The linear branch of 6.1: the actual full-Borel-core enlargement is the
original starred endpoint, including field size two. -/
theorem localEnlargement_eq_star_of_linear (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* PSL(2,F)) :
    localEnlargement d = d.Pstar := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let R := B.pCoreIn 2
  have hn : R ≤ normalizer (d.Pstar : Set G) :=
    ((pCoreIn_le 2 B).trans hBP).trans
      ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)
  have hTR : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ R :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  have hT : (d.sylow : Subgroup d.Pstar) = R.subgroupOf d.Pstar :=
    (d.sylow.is_maximal' (isPGroup_pCoreIn 2 B).comap_subtype
      (fun _ hx => hTR (mem_map_of_mem d.Pstar.subtype hx))).symm
  have hBR : (normalizer (d.sylow : Set d.Pstar)).map d.Pstar.subtype ≤ normalizer (R : Set G) := by
    rw [← source_star_borel d,subgroupOf_map_subtype]
    exact inf_le_left.trans
      (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  let f : d.Pstar →* PSL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.Pstar))
  let a : R → MulAut PSL(2,F) := fun r => MulAut.congr e
    (pCoreJoinAction 2 hn (inclusion le_sup_right r))
  have ha (r : R) (x : d.Pstar) : a r (f x) =
      f (d.Pstar.normalizerMonoidHom ⟨r,hn r.property⟩ x) := by
    change e (pCoreJoinAction 2 hn (inclusion le_sup_right r)
      (e.symm (e (QuotientGroup.mk' (pCore 2 d.Pstar) x)))) = _
    rw [e.symm_apply_apply,pCoreJoinAction_mk]
    rfl
  obtain ⟨T,_,hdisp⟩ := NormalSylowQuotientAction.quotient_displacements_of_local_sylow
    R d.Pstar hn d.sylow hT hBR f (e.surjective.comp (QuotientGroup.mk'_surjective _)) a ha
  have hi (r : R) : pCoreJoinAction 2 hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (d.Pstar ⧸ pCore 2 d.Pstar) := by
    have hh := Matrix.ProjectiveSpecialLinearGroup.inner_of_normalizer_displacements
      F T (a r) (hdisp r).1 (hdisp r).2
    obtain ⟨b,hb⟩ := hh
    obtain ⟨c,hc⟩ := (MulAut.congr_inner_iff e _).mp ⟨b,hb.symm⟩
    exact ⟨c,hc.symm⟩
  have hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥ := by
    apply bot_unique
    intro z hz
    have he : e z ∈ center PSL(2,F) := (centerCongr e ⟨z,hz⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  have hm := map_subgroupOf_pCoreJoin_eq_top_of_inner d.Pstar R hn (isPGroup_pCoreIn 2 B) hz hi
  have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 (d.Pstar ⊔ R : Subgroup G)))) hm
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hc
  have hh := congrArg (Subgroup.map (d.Pstar ⊔ R).subtype) hc
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show d.Pstar ≤ d.Pstar ⊔ R from le_sup_left),
    ←MonoidHom.range_eq_map,range_subtype] at hh
  change d.Pstar ⊔ (localEnlargement d).pCoreIn 2 = localEnlargement d at hh
  rw [localEnlargement_core d,sup_eq_left.mpr (source_core_le_star d)] at hh
  exact hh.symm

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem reduced_borel_core_sylow_in_original (h : HypothesisF11 L S) :
    ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup (commonBorel L (SuzukiContainment.reducedSylow L S))) =
        pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
  apply f11_borel_core_sylow (SuzukiContainment.reduced_hypothesis h)
  exact (normal_subgroupOf_iff_le_normalizer
    (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
      from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)

/-- The intrinsic Sylow span of the reduced endpoint is its actual original
enlargement; the equality is in the original completion. -/
theorem reduced_sylowGenerated_eq (h : HypothesisF11 L S) (i : Fin 2) :
    sylowGenerated (P₀ L S i) = enlargedEndpoint L S i := by
  rw [P₀_eq_source h i, ←reduced_localEnlargement_eq h i]
  apply (localEnlargement_eq_sylowGenerated
    ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i)
    (reduced_borel_core_sylow_in_original h) ?_).symm
  obtain ⟨T,hT⟩ := (SuzukiContainment.reduced_hypothesis h).sylow_parabolic i
  exact ⟨T,hT.le.trans le_sup_right⟩

/-- In the linear branch the reduced source enlargement is the ORIGINAL
starred parabolic. No finiteness of the completion is imposed. -/
theorem reduced_enlargedEndpoint_eq_starred_of_linear (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have he := localEnlargement_eq_star_of_linear (hh.starredLocalRankOneData i)
    (reduced_borel_core_sylow_in_original h) ((hh.starredQuotientEquiv i).symm.trans e)
  rw [reduced_localEnlargement_eq h i] at he
  exact he.trans (SuzukiContainment.reduced_starredParabolic h i)

open Subgroup.CosetGeometry.RankTwo

/-- The graph actor embeds onto the original Chapter 6 enlargement. -/
theorem reduced_graphLocalGroup_image (h : HypothesisF11 L S) (i : Bool) :
    (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map (G₀ L S).subtype =
      family (enlargedEndpoint L S) i := by
  let := finite_endpoints (reduced_triple h)
  let : Finite (reducedFamily L S i) :=
    (finite_endpoints (reduced_triple h) i)
  change (sylowGenerated (MulAction.stabilizer (G₀ L S)
    (Subgroup.CosetGeometry.base (reducedFamily L S) i))).map _ = _
  rw [Subgroup.CosetGeometry.stabilizer_base]
  rw [←sylowGenerated_map_of_injective _ (G₀ L S).subtype_injective]
  cases i
  · change sylowGenerated (((P₀ L S 0).subgroupOf (G₀ L S)).map (G₀ L S).subtype) = _
    rw [map_subgroupOf_eq_of_le (show P₀ L S 0 ≤ G₀ L S from le_sup_left),
      reduced_sylowGenerated_eq h]
    rfl
  · change sylowGenerated (((P₀ L S 1).subgroupOf (G₀ L S)).map (G₀ L S).subtype) = _
    rw [map_subgroupOf_eq_of_le (show P₀ L S 1 ≤ G₀ L S from le_sup_right),
      reduced_sylowGenerated_eq h]
    rfl

/-- The original quotient inclusion, with the graph's two orbit labels. -/
def originalStarredQuotientEquiv (h : HypothesisF11 L S) (i : Bool) :
    (family L i ⧸ pCore 2 (family L i)) ≃*
      (family (starredParabolic L S) i ⧸ pCore 2 (family (starredParabolic L S) i)) := by
  cases i
  · exact h.starredQuotientEquiv 0
  · exact h.starredQuotientEquiv 1

/-- On each original local element this is the literal starred inclusion. -/
theorem originalStarredQuotientEquiv_mk (h : HypothesisF11 L S) (i : Bool)
    (x : family L i) :
    originalStarredQuotientEquiv h i (QuotientGroup.mk x) =
      QuotientGroup.mk (inclusion (show family L i ≤ family (starredParabolic L S) i from
        by cases i <;> exact local_le_starredParabolic _) x) := by
  cases i <;> rfl

/-- In the linear case, the original inclusion identifies the graph actor
with the original starred endpoint, not an abstract replacement. -/
def reduced_linearActorEquiv (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,F)) :
    graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ≃*
      family (starredParabolic L S) i := by
  have he : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
      (G₀ L S).subtype = family (starredParabolic L S) i := by
    rw [reduced_graphLocalGroup_image h]
    cases i
    · exact reduced_enlargedEndpoint_eq_starred_of_linear h 0 e
    · exact reduced_enlargedEndpoint_eq_starred_of_linear h 1 e
  exact ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr he)

/-- The actor equivalence retains each original completion element. -/
theorem reduced_linearActorEquiv_coe (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,F))
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    (reduced_linearActorEquiv h i e x : G) = (x : G₀ L S) := by rfl

/-- The original linear quotient marking on the actual graph actor. -/
def reduced_graphLinearQuotient (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,F)) :
    (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃* PSL(2,F) :=
  (QuotientGroup.congr _ _ (reduced_linearActorEquiv h i e)
    (pCore_map_iso 2 _)).trans ((originalStarredQuotientEquiv h i).symm.trans e)

/-- The quotient map agrees on representatives with the original starred
quotient inclusion and the original model marking. -/
theorem reduced_graphLinearQuotient_mk (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,F))
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    reduced_graphLinearQuotient h i e (QuotientGroup.mk x) =
      e ((originalStarredQuotientEquiv h i).symm (QuotientGroup.mk (reduced_linearActorEquiv h i e x))) :=
  by rfl

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
