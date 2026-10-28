module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneSeeds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaGeneration

/-!
# The critical-center image is the full Sylow omega-center

In the literal beta local quotient, the elementary critical center escapes
the two-core. The full edge normalizer preserves that center. Involution
fusion in each actual rank-one model makes its normalizer span the complete
Sylow omega-center, so invariance identifies the center image with it.
The proof retains the given local Sylow and the actual core quotient map.

This proves (11.2)(b) at prime two before selecting the alpha row, including
the small Suzuki and both unitary covers in the earlier catalogue. It gives
the actor placement needed for the subsequent two-seed fixed-space argument;
it does not assert the pair quotient's model or the core splitting.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)(b), printed p.168, using the rank-one facts (5.2)--(5.5).
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- DGS (11.2)(b), with the original local Sylow and the literal two-core quotient. -/
theorem source_rankOne_center_image_omega
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (T : Sylow 2 (d.localGroup b))
    (hT : (T : Subgroup (d.localGroup b)).map (d.localGroup b).subtype =
      (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2) :
    ((Z (family P) a).subgroupOf (d.localGroup b)).map (QuotientGroup.mk' (pCore 2 (d.localGroup b))) =
      omegaCenterIn ((T : Subgroup (d.localGroup b)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup b)))) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let E := stabilizer (family P) b ⊓ stabilizer (family P) a
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) b from inf_le_left))
    (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hZaE : Z (family P) a ≤ E := le_inf
    ((((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)) (Z_le_stabilizer _ a)
  have hZaT : Z (family P) a ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    exact pGroup_le_core_of_core_sylow E _ hZaE (IsElementaryAbelian.isPGroup 2 _)
      (source_edge_core_sylow h hB hab.symm)
  have hZaL : Z (family P) a ≤ L := hZaT.trans (map_subtype_le _)
  let A := (Z (family P) a).subgroupOf L
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hZaL
  let q := QuotientGroup.mk' (pCore 2 L)
  have hAT : A ≤ (T : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hZaT hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hn : normalizer (T : Set L) ≤ normalizer (A : Set L) := by
    rw [←(source_edge_local_normalizer h d hab.symm Mb T hT).2]
    intro x hx
    exact le_normalizer_comap L.subtype
      (((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a)) hx)
  have hspan : conjugateSpanBy A (normalizer (T : Set L)) = A :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hne : A.map q ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply hc.2
    have hh := map_mono (f := L.subtype) hk
    rw [map_subgroupOf_eq_of_le hZaL] at hh
    exact (hh.trans_eq (localGroup_core_eq (family P) d b)).trans (source_Z_Q_U h b).2
  have hp := source_rank_one_omega_preimage q (QuotientGroup.mk'_surjective _) Mb T
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal T) A hAT hne
  rw [hspan] at hp
  have hm := congrArg (map q) hp
  have hk : q.ker.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),Subgroup.map_sup,hk,sup_bot_eq] at hm
  exact hm.symm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
