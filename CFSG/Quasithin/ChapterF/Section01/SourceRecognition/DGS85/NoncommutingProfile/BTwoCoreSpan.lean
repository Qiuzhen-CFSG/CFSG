module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoGeometry
/-!
# The b=2 core span from the earlier Sylow products

The source 7.1/10.1(c) products Z_t Q_w and Z_w Q_t are Sylows of
the full endpoint stabilizers. Each normalizes the middle core Q_v,
so Sylow maximality contains Q_v in both products. Two factorizations
then give Q_v = Z_w Z_t (Q_w ∩ Q_t), provided the literal intersection
lies in Q_v. Only the actual kernel Sylows are used for short-distance
center placement; the cores remain distinct from permutation kernels.

This proves the span used in 10.6 from genuine earlier Sylow conclusions.
The source D=Z identity, still a separate 10.4 obligation, supplies the
intersection containment in the noncentral branch.
Source: DGS, *Groups and Graphs* (1985), 10.1(c), 10.4 and 10.6,
printed pp.154--157.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

private theorem core_normalized (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) :=
  (stabilizer F v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

private theorem core_le_adjacent (h : LocallyRankOneTriple P B)
    {v w : Vertex F} (he : (graph F).Adj v w) : Q F v ≤ stabilizer F w :=
  (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F he).trans inf_le_right)

/-- The full-vertex Sylow product from 7.1 contains the intermediate core.
The full local permutation kernel is used only to place that core. -/
theorem bTwo_core_cover_of_sylow_product (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x)) (hb : b F = 2)
    {t v w : Vertex F} (htv : (graph F).Adj t v) (hvw : (graph F).Adj v w)
    (hs : Stellmacher.IsSylowSubgroupIn (Z F t ⊔ Q F w) (stabilizer F w)) :
    Q F v ≤ Z F t ⊔ Q F w := by
  let := finite_endpoints h
  let E := stabilizer F w
  obtain ⟨R,hR⟩ := hs
  have hQE : Q F v ≤ E := core_le_adjacent h hvw
  have hnorm : Z F t ⊔ Q F w ≤ normalizer (Q F v : Set G) := by
    apply sup_le
    · exact (graph_Z_le_Q_of_short h hS
        (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv,hb]; decide)).trans
          (Q F v).le_normalizer
    · exact (core_le_adjacent h hvw.symm).trans (core_normalized v)
  have hnorm' : (R : Subgroup E) ≤ normalizer ((Q F v).subgroupOf E : Set E) := by
    rw [←subgroupOf_normalizer_eq hQE]
    intro x hx
    exact hnorm (hR ▸ mem_map_of_mem E.subtype hx)
  have he := R.is_maximal' (R.isPGroup'.to_sup_of_normal_right'
    (isPGroup_pCoreIn 2 (stabilizer F v)).comap_subtype hnorm') le_sup_left
  have hm := map_mono (f := E.subtype) ((le_sup_right : (Q F v).subgroupOf E ≤
    (R : Subgroup E) ⊔ (Q F v).subgroupOf E).trans he.le)
  rwa [map_subgroupOf_eq_of_le hQE,hR] at hm

/-- The two earlier Sylow products prove the source core span. The only
additional intersection premise places the literal D inside the middle core. -/
theorem bTwo_core_span_of_sylow_products (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x)) (hb : b F = 2)
    {t v w : Vertex F} (htv : (graph F).Adj t v) (hvw : (graph F).Adj v w)
    (hsw : Stellmacher.IsSylowSubgroupIn (Z F t ⊔ Q F w) (stabilizer F w))
    (hst : Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F t) (stabilizer F t))
    (hD : D F w t ≤ Q F v) :
    Q F v = (Z F w ⊔ Z F t) ⊔ D F w t := by
  let := finite_endpoints h
  have hZt : Z F t ≤ Q F v := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv,hb]; decide)
  have hZw : Z F w ≤ Q F v := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw.symm,hb]; decide)
  have hcoverw := bTwo_core_cover_of_sylow_product h hS hb htv hvw hsw
  have hcovert := bTwo_core_cover_of_sylow_product h hS hb hvw.symm htv.symm hst
  have hnormt : Z F t ≤ normalizer (Q F w : Set G) :=
    hZt.trans ((core_le_adjacent h hvw).trans (core_normalized w))
  have hnormw : Z F w ≤ normalizer (Q F t : Set G) :=
    hZw.trans ((core_le_adjacent h htv.symm).trans (core_normalized t))
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (Z F t : Set G) * (Q F w : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hnormt]
      exact hcoverw hx
    obtain ⟨a,ha,y,hy,rfl⟩ := hxprod
    have hyv : y ∈ Q F v := by
      simpa only [inv_mul_cancel_left] using (Q F v).mul_mem ((Q F v).inv_mem (hZt ha)) hx
    have hyprod : y ∈ (Z F w : Set G) * (Q F t : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hnormw]
      exact hcovert hyv
    obtain ⟨c,hc,d,hd,rfl⟩ := hyprod
    have hcw : c ∈ Q F w :=
      ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hc)).1
    have hdw : d ∈ Q F w := by
      simpa only [inv_mul_cancel_left] using (Q F w).mul_mem ((Q F w).inv_mem hcw) hy
    exact ((Z F w ⊔ Z F t) ⊔ D F w t).mul_mem
      (mem_sup_left (mem_sup_right ha))
      (((Z F w ⊔ Z F t) ⊔ D F w t).mul_mem
        (mem_sup_left (mem_sup_left hc)) (mem_sup_right ⟨hdw,hd⟩))
  · exact sup_le (sup_le hZw hZt) hD

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
