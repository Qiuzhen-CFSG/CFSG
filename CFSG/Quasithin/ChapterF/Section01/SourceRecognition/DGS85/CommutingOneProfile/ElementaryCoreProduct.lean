module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOmegaImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementarySelection

/-!
# The edge-core product in the elementary beta branch

If the literal edge quotient S/Q_beta is elementary, its identification
with a Sylow of the beta local quotient makes that Sylow elementary.
The critical-center image, already identified with its full omega-center,
is therefore the whole Sylow. Pulling back along the actual quotient gives
S = Z_alpha Q_beta and hence S = Q_alpha Q_beta.

This proves the (11.4) premise needed in (11.7), without selecting either
endpoint as linear or assuming (11.3)(h). The independent pair-span theorem
then selects alpha in ElementaryPathProfile. The nonelementary branch of
(11.4) still requires the source order comparison.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)(b), (11.4), (11.7), printed pp.168,171,174.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- In the elementary beta branch the critical center supplements the beta core
in the actual edge Sylow. The alpha quotient has not been selected. -/
theorem source_elementary_beta_center_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (helem : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf
          ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2))) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Z (family P) a ⊔ Q (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let K := d.localGroup b
  let : Finite K := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  rw [inf_comm (stabilizer (family P) a) (stabilizer (family P) b)] at helem ⊢
  obtain ⟨hN,helem⟩ := helem
  let := hN
  let := helem
  obtain ⟨U,⟨e⟩⟩ := source_edge_core_quotient_sylow h hB d hab.symm
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  let q := QuotientGroup.mk' (pCore 2 K)
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  let : IsElementaryAbelian 2 T' := IsElementaryAbelian.of_surjective
    (U.equiv T').toMonoidHom (U.equiv T').surjective
  have hom : omegaCenterIn (T' : Subgroup (K ⧸ pCore 2 K)) = T' := by
    apply le_antisymm
    · intro x hx
      exact ((mem_omegaCenterIn_iff _ _).mp hx).1
    intro x hx
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hx,?_,elemPow_eq_one_of_isElementaryAbelian x hx⟩
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : T') (⟨x,hx⟩ : T'))
  have him := source_rankOne_center_image_omega h hB d hc hb Mb T hT
  change ((Z (family P) a).subgroupOf K).map q = omegaCenterIn (T' : Subgroup _) at him
  rw [hom] at him
  have hp := congrArg (Subgroup.comap q) him
  change (((Z (family P) a).subgroupOf K).map q).comap q =
    ((T : Subgroup K).map q).comap q at hp
  rw [comap_map_eq,comap_map_eq,QuotientGroup.ker_mk',
    sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] at hp
  have hZK : Z (family P) a ≤ K := by
    apply pGroup_le_localGroup (family P) d b _ (IsElementaryAbelian.isPGroup 2 _)
    exact (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hm := congrArg (Subgroup.map K.subtype) hp
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hZK,hT] at hm
  exact hm.symm.trans (congrArg (Z (family P) a ⊔ ·)
    (localGroup_core_eq (family P) d b))


/-- Source (11.4) under the literal branch hypothesis of (11.7). -/
theorem source_elementary_beta_core_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (helem : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf
          ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2))) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b := by
  have hab := source_critical_one_adjacent hc hb
  apply le_antisymm
  · rw [source_elementary_beta_center_supplement h hB d hc hb Mb helem]
    exact sup_le (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans le_sup_left) le_sup_right
  · exact sup_le (Noncommuting.graph_Q_le_edgeCore h hab)
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
