module
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Mathlib.GroupTheory.Frattini
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.MinimalParabolicGeneration
/-!
# The rank-one Sylow overgroup through a Frattini kernel

A Frattini kernel cannot create a proper supplement, so unique maximality
above a Sylow subgroup lifts through it. Removing the two-core first gives
the exact O₂,Φ-kernel form used in the Baumann-selected group. Normal
extension then gives the minimal-parabolic condition, with nonnormality
certified by the actual SL₂ Sylow image.

Source: Aschbacher–Smith C.1.26, p.132, with B.6.8 and B.6.10.
-/
public section
open Subgroup
namespace Subgroup
variable {G A : Type*} [Group G] [Group A] [Finite G]

theorem hasUniqueMaximalOver_of_frattini_kernel (f : G →* A)
    (hf : Function.Surjective f) {S : Subgroup G}
    (hk : f.ker ≤ frattini G) (h : Order.HasUniqueMaximalOver (S.map f) ⊤) :
    Order.HasUniqueMaximalOver S ⊤ := by
  let : Finite A := Finite.of_surjective f hf
  obtain ⟨M,hM,hu⟩ := h.2
  have hco := isCoatom_comap_of_surjective hf hM.2.isCoatom
  have hSM : S ≤ M.comap f := map_le_iff_le_comap.mp hM.1
  refine ⟨lt_of_le_of_lt hSM hco.lt_top,M.comap f,⟨hSM,hco.covBy_top⟩,?_⟩
  intro V hV
  have hp : V.map f < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hs : V ⊔ f.ker = ⊤ := by
      have hh := congrArg (comap f) he
      simpa only [comap_map_eq,comap_top] using hh
    have hphi : V ⊔ frattini G = ⊤ := top_unique (hs ▸ sup_le_sup_left hk V)
    exact hV.2.ne (frattini_nongenerating hphi)
  have hm : V ≤ M.comap f := map_le_iff_le_comap.mp (h.le_maximal hM (map_mono hV.1) hp)
  exact ((hV.2.eq_or_eq hm le_top).resolve_right hco.1).symm

open scoped MatrixGroups

theorem rankOne_unique_of_coreFrattini_kernel
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (f : G →* SL(2,F)) (hf : Function.Surjective f)
    (hk : f.ker ≤ (frattini (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)))
    (S : Sylow 2 G) : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤ := by
  have hc : pCore 2 G ≤ f.ker := by
    apply (map_eq_bot_iff (pCore 2 G)).mp
    apply bot_unique
    exact (show (pCore 2 G).map f ≤ pCore 2 SL(2,F) from
      le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩).trans_eq
      (Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot (F := F))
  let q := QuotientGroup.mk' (pCore 2 G)
  let g := QuotientGroup.lift (pCore 2 G) f hc
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨q x,rfl⟩
  have hgk : g.ker ≤ frattini (G ⧸ pCore 2 G) := by
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
    exact hk hx
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  let Sg := Sq.mapSurjective hg
  have hu := hasUniqueMaximalOver_of_frattini_kernel g hg hgk
    (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver (F := F) 2 Sg)
  apply hasUniqueMaximalOver_of_surjective q (QuotientGroup.mk'_surjective _) ?_ hu
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.le_sylow_of_normal S


theorem minimal_over_normal_rankOne_frattini
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (L : Subgroup G) [L.Normal] (S : Sylow 2 G)
    (hgen : L ⊔ (S : Subgroup G) = ⊤)
    (f : L →* SL(2,F)) (hf : Function.Surjective f)
    (hk : f.ker ≤ (frattini (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))) :
    (⊤ : Subgroup G) ∈ nonNormalUniqueMaximalOvergroups (S : Subgroup G) := by
  obtain ⟨U,hU⟩ := S.exists_subgroupOf_eq_of_normal L
  have hu := rankOne_unique_of_coreFrattini_kernel F f hf hk U
  have huL := hasUniqueMaximalOver_map_subtype hu
  rw [hU,subgroupOf_map_subtype,inf_comm] at huL
  have huG := hasUniqueMaximalOver_sup_of_normalizes
    (show (S : Subgroup G) ≤ normalizer (L : Set G) from le_normalizer_of_normal) huL
  rw [hgen] at huG
  refine ⟨huG,?_⟩
  intro hn
  let : (S : Subgroup G).Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hnU : (U : Subgroup L).Normal := by rw [hU]; infer_instance
  exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 (U.mapSurjective hf)
    (Normal.map hnU f hf)

end Subgroup
