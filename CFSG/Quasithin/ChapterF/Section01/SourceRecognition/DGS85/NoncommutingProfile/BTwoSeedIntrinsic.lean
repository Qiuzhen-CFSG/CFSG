module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedMovement

/-!
# Intrinsic descriptions of D and the central seed

Local normality and transitivity on neighbors identify D with the
intersection of all neighboring cores. The same argument identifies the
seed with the span of all neighboring radius/core factors together with D.
These formulas remove the choice of opposite neighbor and show that both
subgroups are normalized by the full vertex stabilizer of the source graph.

The constructions retain Q_delta=O2(G_delta), not the larger permutation
kernel. Seed saturation with Q_alpha remains a separate obligation.
Source: DGS, Groups and Graphs (1985), 10.4 and the seed in the proof
of 10.7, printed pp.155--156 and158--159.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- D is the intersection of all neighboring cores, not just the two used
in its initial definition. -/
theorem BTwoCenterActionData.D_eq_neighbor_core_intersection
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    D F m t = ⨅ x : Vertex F, ⨅ (_ : (graph F).Adj v x), Q F x := by
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hn := hd ▸ d.normalized h hS hb
  apply le_antisymm
  · apply le_iInf
    intro x
    apply le_iInf
    intro hx
    by_cases hxm : x = m
    · subst x
      exact inf_le_left
    obtain ⟨a,ha,_⟩ := c.exists_opposite_lift h hx hxm
    have hm := map_mono (f := (MulAut.conj (a : G)).toMonoidHom)
      (show D F m t ≤ Q F m from inf_le_left)
    have hnmap : (D F m t).map (MulAut.conj (a : G)).toMonoidHom = D F m t :=
      mem_normalizer_iff_map_conj_eq.mp (hn a.property)
    rwa [hnmap,←Q_translate,ha] at hm
  · exact le_inf (iInf_le_of_le m (iInf_le_of_le c.middle le_rfl))
      (iInf_le_of_le t (iInf_le_of_le ht le_rfl))

/-- Every neighboring radius/core factor lies in the same seed. Thus the
seed has an intrinsic description independent of the opposite lift. -/
theorem BTwoCenterActionData.seed_eq_neighbor_span
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    centralSeed F v m t =
      (⨆ x : Vertex F, ⨆ (_ : (graph F).Adj v x), V F x 1 ⊓ Q F v) ⊔ D F m t := by
  let := finite_endpoints h
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hn := hd ▸ d.seed_normalized h hS hb (hd.symm ▸ c.actor_le)
  have hfactor (x : Vertex F) (hx : (graph F).Adj v x) :
      V F x 1 ⊓ Q F v ≤ ⨆ y : Vertex F, ⨆ (_ : (graph F).Adj v y), V F y 1 ⊓ Q F v :=
    le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  apply le_antisymm
  · exact sup_le (sup_le ((hfactor m c.middle).trans le_sup_left)
      ((hfactor t ht).trans le_sup_left)) le_sup_right
  · apply sup_le _ le_sup_right
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hxm : x = m
    · subst x
      exact le_sup_left.trans le_sup_left
    obtain ⟨a,ha,_⟩ := c.exists_opposite_lift h hx hxm
    have hav : (a : G) • v = v := c.actor_le a.property
    have hm := map_mono (f := (MulAut.conj (a : G)).toMonoidHom)
      (show V F m 1 ⊓ Q F v ≤ centralSeed F v m t from le_sup_left.trans le_sup_left)
    have hnmap : (centralSeed F v m t).map (MulAut.conj (a : G)).toMonoidHom = centralSeed F v m t :=
      mem_normalizer_iff_map_conj_eq.mp (hn a.property)
    rwa [map_inf _ _ _ (MulAut.conj (a : G)).injective,←V_translate,←Q_translate,
      ha,hav,hnmap] at hm

private theorem adjacent_of_stabilizer (v x : Vertex F)
    (g : G) (hg : g ∈ stabilizer F v) (hx : (graph F).Adj v x) :
    (graph F).Adj v (g • x) := by
  have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hx
  change (graph F).Adj (g • v) (g • x) at hh
  rwa [hg] at hh

/-- The intrinsic denominator is normal in the full original vertex stabilizer. -/
theorem BTwoCenterActionData.D_stabilizer_normalized
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    stabilizer F v ≤ normalizer (D F m t : Set G) := by
  have he := c.D_eq_neighbor_core_intersection h hS hb ht hne
  have hD (x : Vertex F) (hx : (graph F).Adj v x) : D F m t ≤ Q F x := by
    rw [he]
    exact iInf_le_of_le x (iInf_le_of_le hx le_rfl)
  apply le_normalizer_iff.mpr
  intro g hg a ha
  rw [he]
  apply mem_iInf.mpr
  intro x
  apply mem_iInf.mpr
  intro hx
  have hx' := adjacent_of_stabilizer v x g⁻¹ ((stabilizer F v).inv_mem hg) hx
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom (hD (g⁻¹ • x) hx' ha)
  rwa [←Q_translate,smul_inv_smul] at hh

/-- The same intrinsic construction gives full-stabilizer normality of
the numerator, without making the unjustified assertion that it is Q. -/
theorem BTwoCenterActionData.seed_stabilizer_normalized
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    stabilizer F v ≤ normalizer (centralSeed F v m t : Set G) := by
  let := finite_endpoints h
  let N := ⨆ x : Vertex F, ⨆ (_ : (graph F).Adj v x), V F x 1 ⊓ Q F v
  have hnN : stabilizer F v ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg a ha
    have hm : N.map (MulAut.conj g).toMonoidHom ≤ N := by
      dsimp only [N]
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro x
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro hx
      rw [map_inf _ _ _ (MulAut.conj g).injective,←V_translate,←Q_translate,hg]
      exact le_iSup_of_le (g • x) (le_iSup_of_le (adjacent_of_stabilizer v x g hg hx) le_rfl)
    exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  rw [c.seed_eq_neighbor_span h hS hb ht hne]
  exact (le_inf hnN (c.D_stabilizer_normalized h hS hb ht hne)).trans
    (normalizer_inf_normalizer_le_normalizer_sup N (D F m t))

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
