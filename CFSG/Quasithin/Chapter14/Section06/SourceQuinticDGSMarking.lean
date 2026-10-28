module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSCritical
public import CFSG.Quasithin.Chapter14.Section02.ProperSpan
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.KernelIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.KernelControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Transport
public import Theory.GroupTheory.SylowCenterFixedSpan
public import Theory.GroupTheory.AmalgamGraph.SylowCenterEmbedding

/-!
# Literal center, Sylow and critical-path markings for the quintic pair

The reduced graph centers are the original central line and four-plane.
The two full endpoint cores generate the original Sylow.  The central line
at the quintic endpoint determines the direction of criticality: Chapter 8
makes the starting local center trivial, so that start must be cubic.
Translation of the last edge then gives a critical three-path ending at the
literal original base edge.  No path or model marking is an input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

private theorem critical_start_not_central_type
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : CommutingNontrivial.EarlierLocalTheorems (family P))
    (hz : family P false ≤ centralizer (Z (family P) (base (family P) false) : Set G))
    {a x y : Vertex (family P)} (hc : IsCriticalPair (family P) a y)
    (hax : (graph (family P)).Adj a x)
    (hd : (graph (family P)).dist x y + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) y⁆ = ⊥) :
    a.type = true := by
  let F := family P
  have hneighbor := (CommutingNontrivial.source_critical_geometry h d hc hax hd hb hcomm).2.2.1
  have hcenter := CommutingNontrivial.local_center_eq_bot_of_neighbor_central h d hax hneighbor
  by_contra ha
  have hat : a.type = false := Bool.eq_false_iff.mpr ha
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F a
  rw [hat] at hg
  have hcentral : stabilizer F a ≤ centralizer (Z F a : Set G) := by
    rw [←hg,stabilizer_translate,Z_translate,stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    rintro _ ⟨u,hu,rfl⟩ _ ⟨z,hz',rfl⟩
    simpa only [map_mul] using congrArg (MulAut.conj g).toMonoidHom (hz hu z hz')
  have hZlocal : Z F a ≤ d.localGroup a := by
    apply iSup_le
    intro R
    exact (map_subtype_le _).trans (d.sylow_le a R)
  have hZbot : Z F a = ⊥ := by
    apply bot_unique
    intro z hz'
    let zL : d.localGroup a := ⟨z,hZlocal hz'⟩
    have hzc : zL ∈ center (d.localGroup a) := by
      rw [mem_center_iff]
      intro t
      apply Subtype.ext
      exact (hcentral (d.local_le a t.property) z hz').symm
    have hone : zL = 1 := by simpa only [hcenter,mem_bot] using hzc
    exact mem_bot.mpr (congrArg Subtype.val hone)
  exact hc.2 (hZbot ▸ bot_le)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
include hG hempty hM hu hmany hcard e

/-- The two DGS base centers retain the original line and plane, respectively. -/
theorem source_quintic_dgs_center_markings
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let J := Reduction.G₀ ![H,X] (T : Subgroup G)
    let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
    (Z F (base F false)).map J.subtype = centralInvolutions T ∧
      (Z F (base F true)).map J.subtype = localModule T M := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let J := Reduction.G₀ ![H,X] (T : Subgroup G)
  let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
  obtain ⟨_,_,_,_,_,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hcent : H ≤ centralizer (centralInvolutions T : Set G) :=
    (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hseed : omegaCenterIn (((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype) =
      centralInvolutions T := by
    change omegaCenterIn (((T : Subgroup G).subgroupOf H).map H.subtype) = _
    rw [map_subgroupOf_eq_of_le hTH]
    rfl
  have hZH : sylowCenterSpan H = centralInvolutions T := by
    have he := sylowCenterSpan_eq_seed_of_normalized H (T.subtype hTH)
      (by rw [hseed]; exact hcent.trans (Subgroup.centralizer_le_normalizer _))
    exact he.trans hseed
  have hZX : sylowCenterSpan X = localModule T M := by
    rw [sylowCenterSpan_eq_conjugateSpan X X le_rfl (fun _ => map_subtype_le _) (T.subtype hTX),
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX]
    change conjugateSpanBy (centralInvolutions T) X = localModule T M
    apply le_antisymm
    · exact conjugateSpanBy_mono le_rfl (sup_le (sourceResidual_le M Mc) hM.1.2)
    · rw [Section02.source_plane_module_residual_span hG T hempty hM hu hmany hcard e]
      exact conjugateSpanBy_mono le_rfl le_sup_left
  constructor
  · rw [Z,stabilizer,Subgroup.CosetGeometry.stabilizer_base,
      ←sylowCenterSpan_map_of_injective J.subtype J.subtype_injective,(hmaps false).1]
    exact hZH
  · rw [Z,stabilizer,Subgroup.CosetGeometry.stabilizer_base,
      ←sylowCenterSpan_map_of_injective J.subtype J.subtype_injective,(hmaps true).1]
    exact hZX

/-- The original full cores generate the original Sylow; the same subgroup is
the embedded common Sylow at both literal reduced endpoints. -/
theorem source_quintic_dgs_common_sylow
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let J := Reduction.G₀ ![H,X] (T : Subgroup G)
    let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
    H.pCoreIn 2 ⊔ X.pCoreIn 2 = T ∧
      Q F (base F false) ⊔ Q F (base F true) = (T : Subgroup G).subgroupOf J ∧
      ∀ i, ∃ S : Sylow 2 (F i),
        (S : Subgroup (F i)).map (F i).subtype = Q F (base F false) ⊔ Q F (base F true) ∧
        ((S : Subgroup (F i)).map (F i).subtype).map J.subtype = T := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let J := Reduction.G₀ ![H,X] (T : Subgroup G)
  let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    exact (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq (map_subgroupOf_eq_of_le hTH)
  have hBT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    exact (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq (map_subgroupOf_eq_of_le hTX)
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hBi : (X.pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
    let P := T.subtype hTX
    have hm := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal P)
    rw [SymmetricThreeTwoCore.sylow_index_three eX P,SymmetricThreeTwoCore.core_index eX] at hm
    have hi' : (pCore 2 X).relIndex (P : Subgroup X) = 2 := by omega
    have hmap : (P : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTX
    rw [←hmap,pCoreIn,relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hi'
  have hcross := Section02.SolvableAmalgam.source_quintic_crossing_core_index
    hG T hempty hM hu hmany hcard e H hH hi
  have hnot : ¬ H.pCoreIn 2 ≤ X.pCoreIn 2 := by
    intro hh
    have hone : (H.pCoreIn 2 ⊓ X.pCoreIn 2).relIndex (H.pCoreIn 2) = 1 :=
      relIndex_eq_one.mpr (le_inf le_rfl hh)
    change (H.pCoreIn 2 ⊓ X.pCoreIn 2).relIndex (H.pCoreIn 2) = 2 at hcross
    omega
  have hjoin : H.pCoreIn 2 ⊔ X.pCoreIn 2 = (T : Subgroup G) := by
    have hle := sup_le hQT hBT
    have hm := relIndex_mul_relIndex (X.pCoreIn 2) (H.pCoreIn 2 ⊔ X.pCoreIn 2)
      (T : Subgroup G) le_sup_right hle
    rw [hBi] at hm
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hp | hp
    · exact le_antisymm hle (relIndex_eq_one.mp hp.2)
    · exact (hnot (le_sup_left.trans (relIndex_eq_one.mp hp.2))).elim
  obtain ⟨_,_,_,_,_,hJ,hmaps,_,S,hS⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change J = H ⊔ X at hJ
  have hTJ : (T : Subgroup G) ≤ J := by rw [hJ]; exact hTH.trans le_sup_left
  have hjoinMap : (Q F (base F false) ⊔ Q F (base F true)).map J.subtype = T := by
    rw [Subgroup.map_sup,(hmaps false).2,(hmaps true).2]
    exact hjoin
  have hgraph : Q F (base F false) ⊔ Q F (base F true) = (T : Subgroup G).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hjoinMap,map_subgroupOf_eq_of_le hTJ]
  refine ⟨hjoin,hgraph,?_⟩
  intro i
  have hSF : (S : Subgroup J) ≤ F i := by
    apply (Subgroup.map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hS,(hmaps i).1]
    cases i
    · exact hTH
    · exact hTX
  refine ⟨S.subtype hSF,?_,?_⟩
  · rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSF]
    apply map_injective J.subtype_injective
    exact hS.trans hjoinMap.symm
  · rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSF]
    exact hS

set_option maxHeartbeats 800000 in
/-- A genuine directed critical three-path ends at the original cubic-to-quintic
base edge, with the original nonzero displacement transported by one element. -/
theorem source_quintic_dgs_critical_path
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
    ∃ a x : Vertex F,
      a.type = true ∧ x.type = false ∧
      (graph F).Adj a x ∧ (graph F).Adj x (base F true) ∧
      x ≠ base F false ∧ a ≠ base F true ∧
      IsCriticalPair F a (base F false) ∧ (graph F).dist x (base F false) = 2 ∧
      ⁅Z F a,Z F (base F false)⁆ = ⊥ ∧
      ⁅V F x 1 ⊓ Q F (base F false),V F (base F false) 1⁆ ≠ ⊥ := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let J := Reduction.G₀ ![H,X] (T : Subgroup G)
  let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
  obtain ⟨hF,_,_,_,_,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  have hZmap := (source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi).1
  have hHmap : (F false).map J.subtype = H := (hmaps false).1
  change (Z F (base F false)).map J.subtype = centralInvolutions T at hZmap
  have hcent := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hcentral : F false ≤ centralizer (Z F (base F false) : Set J) := by
    intro u hu' z hz'
    apply J.subtype_injective
    exact hcent (by rw [←hHmap]; exact mem_map_of_mem J.subtype hu')
      (z : G) (by rw [←hZmap]; exact mem_map_of_mem J.subtype hz')
  obtain ⟨hb,a,x,y,hc,hax,hd,hcomm,hdisp⟩ :=
    source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi
  have ht := Reduction.reduced_triple hF
  have ha : a.type = true := critical_start_not_central_type ht
    (Reduction.reducedFullEarlierLocalTheorems hF) hcentral hc hax hd
    (by change 1 < b F; change b F = 3 at hb; omega) hcomm
  have hx : x.type = false := by
    cases hx : x.type
    · rfl
    · exact (hax.1 (ha.trans hx.symm)).elim
  have hxy : (graph F).dist x y = 2 := by
    change (graph F).dist x y + 1 = b F at hd
    change b F = 3 at hb
    omega
  have hy : y.type = false := by
    have hh := (even_dist_iff F ht.generate x y).mp (by rw [hxy]; decide)
    exact hh.symm.trans hx
  obtain ⟨m,hym,hdm⟩ := exists_predecessor F ht.generate x y (by
    intro he
    rw [he,SimpleGraph.dist_self] at hxy
    contradiction)
  have hxm : (graph F).Adj x m := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have hm : m.type = true := by
    cases hm : m.type
    · exact (hym.1 (hy.trans hm.symm)).elim
    · rfl
  obtain ⟨g,hgm,hgy⟩ := incident_common_translate F hym.symm.2
  rw [hm] at hgm
  rw [hy] at hgy
  have hgy' : g⁻¹ • y = base F false := by rw [←hgy,inv_smul_smul]
  have hdx : (graph F).dist (g⁻¹ • x) (base F false) = 2 := by
    have hh := dist_smul F g⁻¹ x y
    rw [hgy',hxy] at hh
    exact hh
  have hbranch := CommutingNontrivial.branch_translate F hc hcomm hdisp g⁻¹
  rw [hgy'] at hbranch
  refine ⟨g⁻¹ • a,g⁻¹ • x,?_,?_,?_,?_,?_,?_,hbranch.1,hdx,hbranch.2⟩
  · simpa using ha
  · simpa using hx
  · exact (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hax
  · have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hxm
    change (graph F).Adj (g⁻¹ • x) (g⁻¹ • m) at hh
    rwa [←hgm,inv_smul_smul] at hh
  · intro he
    rw [he,SimpleGraph.dist_self] at hdx
    contradiction
  · intro he
    have hh := hbranch.1.1
    rw [he,hb] at hh
    have hadj : (graph F).Adj (base F true) (base F false) :=
      ⟨by change (true : Bool) ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hh
    contradiction

end CFSG.Quasithin.Chapter14.Section06
