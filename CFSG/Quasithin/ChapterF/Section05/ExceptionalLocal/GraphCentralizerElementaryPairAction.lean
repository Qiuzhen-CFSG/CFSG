module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerAction
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerElementaryTI
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerElementaryPairExclusion
public import Theory.ElementaryAbelian.Join
public import Theory.SpecificGroups.SymmetricFourConjugacy
public import Theory.GroupTheory.IndexTwoPairCard
public import Theory.GroupTheory.CubicPairNormalizerQuotient

/-!
# The elementary pair from a cubic actor centralizing the residual

Let V be the residual centralizer, assumed elementary, and K the actual A6
residual. V commutes with K and meets it trivially. Adjoining each literal
endpoint four-group to V gives an elementary sixteen-group inside R. Their
join is V times the residual D8, so they intersect in order eight.

A supplied normalizer element acts cubically on V and centralizes K. Each
endpoint supplies an element of order three in K normalizing its four-group.
The two cyclic groups commute and meet trivially because K has trivial center.
Their product gives a factor nine in the normalizer order, which survives
quotienting by sixteen. The source elementary-family exclusion now applies.
The ambient supplied actor need not itself have order three.

Source: Aschbacher--Smith F.5.5, printed p.302. The actor construction and
its original-source discharge are owned by the final non-elementarity assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory


namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

private theorem residual_centralizer_inf_residual_eq_one (R : Sylow 2 (C c i)) (hR:Tf c i≤R)
    (x:G) (hxC:x∈centralizer (((pResidual 2 (C c i)).map (C c i).subtype):Set G))
    (hxK:x∈(pResidual 2 (C c i)).map (C c i).subtype) : x=1 := by
  obtain ⟨xC,hxR,rfl⟩ := hxK
  have hx : xC∈centralizer (pResidual 2 (C c i):Set (C c i)) := by
    intro k hk
    apply Subtype.ext
    exact hxC k.val (mem_map_of_mem _ hk)
  have hd := source_residualCentralizer_disjoint_rootComplement c i z h R hR
  have hxJ : xC∈sourceRootComplement c i z h := by
    rw [sourceRootComplement_eq]
    exact mem_sup_left hxR
  exact congrArg Subtype.val (disjoint_def.mp hd hx hxJ)

private theorem residual_centralizer_le_centralizer (R : Sylow 2 (C c i)) (hR:Tf c i≤R) :
    sourceResidualCentralizer c i ≤
      centralizer (((pResidual 2 (C c i)).map (C c i).subtype):Set G) := by
  intro x hx
  rw [sourceResidualCentralizer_eq_point c i z h R hR] at hx
  exact hx.2

omit [Finite G] h in
private theorem sourceEndpointResidualCore_le_K (b:Bool) : sourceEndpointResidualCore c i b≤
    (pResidual 2 (C c i)).map (C c i).subtype := by
  apply le_trans _ (sourceResidualJoin_le_twoResidual c i)
  cases b
  · exact le_sup_left
  · exact le_sup_right

private theorem sourceEndpointResidualCore_elementary (b:Bool) :
    IsElementaryAbelian 2 (sourceEndpointResidualCore c i b) := by
  rw [sourceEndpointResidualCore_eq_map c i h.embedding_injective b]
  exact IsElementaryAbelian.map _

private theorem sourceEndpoint_cubic (b:Bool) :
    ∃ y:G, y∈(pResidual 2 (C c i)).map (C c i).subtype ∧ orderOf y=3 ∧
      y∈normalizer (sourceEndpointResidualCore c i b:Set G) := by
  let p := SymmetricFourConjugacy.threeCycle
  let y := sourceEndpointCoreMap c i h.embedding_injective b p
  have hy3 : orderOf y=3 := (orderOf_injective _
    (sourceEndpointCoreMap_injective c i h.embedding_injective b) p).trans
      SymmetricFourConjugacy.orderOf_threeCycle
  have hyD : y∈Dendpoint c i b := (source_Dendpoint_equiv c i h.embedding_injective b).symm (1,p) |>.property
  let yD : Dendpoint c i b := ⟨y,hyD⟩
  have hyR : yD∈pResidual 2 (Dendpoint c i b) := by
    apply mem_pResidual_of_orderOf_coprime
    rw [←orderOf_coe yD,hy3]
    decide
  let j : Dendpoint c i b →* C c i := inclusion ((Dendpoint_le_E c i b).trans inf_le_right)
  refine ⟨y,⟨j yD,map_pResidual_le 2 j (mem_map_of_mem j hyR),rfl⟩,hy3,?_⟩
  rw [sourceEndpointResidualCore_eq_map c i h.embedding_injective b]
  exact core.le_normalizer_map _ (mem_map_of_mem _ (show p∈normalizer (core:Set (Equiv.Perm (Fin 4))) from
    le_normalizer_of_normal (show p∈(⊤:Subgroup (Equiv.Perm (Fin 4))) from trivial)))

variable [IsElementaryAbelian 2 (sourceResidualCentralizer c i)]
/-- The two literal endpoint cores give elementary sixteen-groups meeting in order eight. -/
theorem source_residualCentralizer_elementary_pair_geometry (R : Sylow 2 (C c i)) (hR:Tf c i≤R) :
    (∀b:Bool, (sourceResidualCentralizer c i ⊔ sourceEndpointResidualCore c i b : Subgroup G)≤Rimage c i R ∧
      IsElementaryAbelian 2 (sourceResidualCentralizer c i ⊔ sourceEndpointResidualCore c i b : Subgroup G) ∧
      Nat.card (sourceResidualCentralizer c i ⊔ sourceEndpointResidualCore c i b : Subgroup G)=16) ∧
    Nat.card ((sourceResidualCentralizer c i ⊔ sourceEndpointResidualCore c i false) ⊓
      (sourceResidualCentralizer c i ⊔ sourceEndpointResidualCore c i true) : Subgroup G)=8 := by
  let V:=sourceResidualCentralizer c i
  let U:=sourceResidualJoin c i
  have hVU : V≤centralizer (U:Set G) :=
    (residual_centralizer_le_centralizer c i z h R hR).trans
      (centralizer_le (show (U:Set G)⊆((pResidual 2 (C c i)).map (C c i).subtype:Set G) from sourceResidualJoin_le_twoResidual c i))
  have hdVU : Disjoint V U := disjoint_def.mpr (fun {x} hxV hxU=>
    residual_centralizer_inf_residual_eq_one c i z h R hR x
      (residual_centralizer_le_centralizer c i z h R hR hxV) (sourceResidualJoin_le_twoResidual c i hxU))
  have hUV : U≤centralizer (V:Set G) := (le_centralizer_iff.mp hVU)
  have hUcard : Nat.card U=8 := by
    rw [Nat.card_congr (sourceResidualJoinEquiv c i h.embedding_injective).toEquiv,DihedralGroup.nat_card]
  have hVcard : Nat.card V=4 := sourceResidualCentralizer_card c i z h R hR
  have hVUcard : Nat.card (V⊔U:Subgroup G)=32 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint V U
      (hUV.trans (Subgroup.centralizer_le_normalizer _)) hdVU,hVcard,hUcard]
  have hF (b:Bool) : sourceEndpointResidualCore c i b≤U := by
    cases b
    · exact le_sup_left
    · exact le_sup_right
  have hB (b:Bool) : (V⊔sourceEndpointResidualCore c i b:Subgroup G)≤Rimage c i R ∧
      IsElementaryAbelian 2 (V⊔sourceEndpointResidualCore c i b:Subgroup G) ∧
      Nat.card (V⊔sourceEndpointResidualCore c i b:Subgroup G)=16 := by
    let := sourceEndpointResidualCore_elementary c i z h b
    have hFV : sourceEndpointResidualCore c i b≤centralizer (V:Set G) := (hF b).trans hUV
    refine ⟨sup_le (sourceResidualCentralizer_le_R c i z h R hR)
      ((hF b).trans ((sourceResidualJoin_le_Tf c i h.embedding_injective).trans
        (normalizer_TfImage_le_Rimage c i R hR))),IsElementaryAbelian.sup_of_le_centralizer hFV,?_⟩
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hFV.trans (Subgroup.centralizer_le_normalizer _)) (hdVU.mono le_rfl (hF b)),hVcard,
      sourceEndpointResidualCore_card c i h.embedding_injective b]
  refine ⟨hB,inf_card_eight_of_card_sixteen_sup_thirtytwo _ _ (hB false).2.2 (hB true).2.2 ?_⟩
  convert hVUcard using 1
  simp only [V,U,sourceResidualJoin,sup_assoc,sup_left_comm,sup_left_idem]

omit [IsElementaryAbelian 2 (sourceResidualCentralizer c i)] in
private theorem elementary_pair_actors (R : Sylow 2 (C c i)) (hR:Tf c i≤R)
    (g : normalizer (sourceResidualCentralizer c i:Set G))
    (hg : (g:G)∈centralizer (((pResidual 2 (C c i)).map (C c i).subtype):Set G))
    (hgo : orderOf ((sourceResidualCentralizer c i).normalizerMonoidHom g)=3)
    (b:Bool) :
    ∃y:G, (g:G)∈normalizer ((sourceResidualCentralizer c i ⊔ sourceEndpointResidualCore c i b:Subgroup G):Set G) ∧
      y∈normalizer ((sourceResidualCentralizer c i ⊔ sourceEndpointResidualCore c i b:Subgroup G):Set G) ∧
      Commute (g:G) y ∧ Disjoint (zpowers (g:G)) (zpowers y) ∧
      3∣orderOf (g:G) ∧ orderOf y=3 := by
  let V:=sourceResidualCentralizer c i
  let F:=sourceEndpointResidualCore c i b
  let K:=(pResidual 2 (C c i)).map (C c i).subtype
  have hVK : V≤centralizer (K:Set G) := residual_centralizer_le_centralizer c i z h R hR
  have hKV : K≤centralizer (V:Set G) := le_centralizer_iff.mp hVK
  have hFK : F≤K := sourceEndpointResidualCore_le_K c i b
  obtain ⟨y,hyK,hy3,hyF⟩ := sourceEndpoint_cubic c i z h b
  have hgF : (g:G)∈centralizer (F:Set G) := centralizer_le hFK hg
  have hgN : (g:G)∈normalizer ((V⊔F:Subgroup G):Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup V F
      ⟨g.property,Subgroup.centralizer_le_normalizer _ hgF⟩
  have hyN : y∈normalizer ((V⊔F:Subgroup G):Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup V F
      ⟨Subgroup.centralizer_le_normalizer _ (hKV hyK),hyF⟩
  have hd : Disjoint (zpowers (g:G)) (zpowers y) := by
    apply disjoint_def.mpr
    intro x hxg hxy
    exact residual_centralizer_inf_residual_eq_one c i z h R hR x
      ((zpowers_le.mpr hg) hxg) ((zpowers_le.mpr hyK) hxy)
  have ho : 3∣orderOf (g:G) := by
    have hh:=orderOf_map_dvd V.normalizerMonoidHom g
    rw [hgo] at hh
    exact (orderOf_coe g) ▸ hh
  exact ⟨y,hgN,hyN,(hg y hyK).symm,hd,ho,hy3⟩

/-- The actual elementary-sixteen pair contradicts the source family, using
only the supplied cubic action on V and pointwise centralization of K. -/
theorem source_elementary_pair_false_of_centralizing_cubic
    (R : Sylow 2 (C c i)) (hR:Tf c i≤R)
    (g : normalizer (sourceResidualCentralizer c i:Set G))
    (hg : (g:G)∈centralizer (((pResidual 2 (C c i)).map (C c i).subtype):Set G))
    (hgo : orderOf ((sourceResidualCentralizer c i).normalizerMonoidHom g)=3) : False := by
  let B (b:Bool) : Subgroup G:=sourceResidualCentralizer c i⊔sourceEndpointResidualCore c i b
  obtain ⟨hB,hi⟩:=source_residualCentralizer_elementary_pair_geometry c i z h R hR
  have h9 (b:Bool) : 9∣Nat.card (normalizer (B b:Set G)⧸
      (B b).subgroupOf (normalizer (B b:Set G))) := by
    obtain ⟨y,hgN,hyN,hgy,hd,ho,hy3⟩:=elementary_pair_actors c i z h R hR g hg hgo b
    exact nine_dvd_normalizer_quotient_of_disjoint_cubics (B b) (hB b).2.2
      g y hgN hyN hgy hd ho hy3
  exact source_elementary_pair_exclusion c i z h R (B false) (B true)
    (hB false).1 (hB true).1 (hB false).2.1 (hB true).2.1
    (hB false).2.2 (hB true).2.2 hi (h9 false) (h9 true)
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
