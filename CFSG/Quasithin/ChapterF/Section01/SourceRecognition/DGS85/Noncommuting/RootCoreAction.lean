module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LastOddSource

/-!
# Opposite cores in the natural local action

At a naturally marked even vertex, a neighboring two-core has nonzero
image in the local Sylow. The full edge normalizes this image, so torus
invariance makes it the whole root group. It therefore acts transitively
on the other neighbors. A noncommuting critical center moves the remaining
neighbor, and together the two groups act transitively on all neighbors.

These are the local action computations used to identify and transport the
radius/core intersection in the last paragraph of DGS (7.5).
Source: DGS, *Groups and Graphs* (1985), (7.5), printed pp.130--131.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_linear_opposite_core_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v a : Vertex (family P)} (ha : (graph (family P)).Adj v a)
    (c : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) a))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : c.Pstar →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q (family P) v).subgroupOf c.Pstar)
    (hesc : ¬ Q (family P) a ≤ Q (family P) v) :
    ((Q (family P) a).subgroupOf c.Pstar).map π =
      (c.sylow : Subgroup c.Pstar).map π := by
  let := c.finite_P
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let S := (stabilizer (family P) v ⊓ stabilizer (family P) a).pCoreIn 2
  have hS : (c.sylow : Subgroup c.Pstar).map c.Pstar.subtype = S :=
    local_sylow_eq_edgeCore c ho (source_edge_core_sylow h hB ha)
  have hSL : S ≤ c.Pstar := hS.symm.le.trans (map_subtype_le _)
  have hQS : Q (family P) a ≤ S := by
    simpa only [S,inf_comm] using graph_Q_le_edgeCore h ha.symm
  have hQL := hQS.trans hSL
  have hs : S.subgroupOf c.Pstar = c.sylow := by
    apply map_injective c.Pstar.subtype_injective
    rw [map_subgroupOf_eq_of_le hSL,hS]
  let T := c.sylow.mapSurjective hπ
  let A := ((Q (family P) a).subgroupOf c.Pstar).map π
  have hAT : A ≤ (T : Subgroup SL(2,k)) := by
    apply map_mono
    rw [←hs]
    exact subgroupOf_mono _ hQS
  have hn : normalizer (c.sylow : Set c.Pstar) ≤
      normalizer ((Q (family P) a).subgroupOf c.Pstar : Set c.Pstar) := by
    rw [←source_star_borel c]
    intro z hz
    apply mem_normalizer_iff.mpr
    intro x
    have hnQ : (z : G) ∈ normalizer (Q (family P) a : Set G) :=
      ((stabilizer (family P) a).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hz.2
    exact mem_normalizer_iff.mp hnQ x
  apply Matrix.SpecialLinearGroup.subgroup_eq_sylow_of_normalizer_invariant T A hAT
  · intro hbot
    have hle := (Subgroup.map_eq_bot_iff _).mp hbot
    rw [hk] at hle
    exact hesc (fun x hx => hle (show (⟨x,hQL hx⟩ : c.Pstar) ∈
      (Q (family P) a).subgroupOf c.Pstar from hx))
  · change normalizer ((c.sylow : Subgroup c.Pstar).map π : Set SL(2,k)) ≤ _
    rw [←c.sylow.normalizer_map_surjective π hπ]
    exact (map_mono hn).trans (((Q (family P) a).subgroupOf c.Pstar).le_normalizer_map π)

theorem graph_natural_opposite_core_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v a : Vertex (family P)} (ha : (graph (family P)).Adj v a)
    (c : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) a))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    (hnat : HasNaturalCenter c.Pstar (Z (family P) v) (Q (family P) v))
    (hob : ¬ stabilizer (family P) a ≤ normalizer
      ((Q (family P) v ⊓ Q (family P) a : Subgroup G) : Set G))
    {x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y) (hxa : x ≠ a) (hya : y ≠ a) :
    ∃ g ∈ Q (family P) a, g • x = y := by
  have hesc : ¬ Q (family P) a ≤ Q (family P) v := by
    intro he
    apply hob
    rw [inf_eq_right.mpr he]
    exact (stabilizer (family P) a).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  obtain ⟨k,_,_,_,π,hπ,hk,_⟩ := hnat
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  exact graph_linear_root_transitive h ha c π hπ hk _
    (graph_linear_opposite_core_image h hB ha c ho π hπ hk hesc) hx hy hxa hya

theorem graph_critical_center_moves_other_neighbor
    (h : LocallyRankOneTriple P B)
    {v w u a : Vertex (family P)}
    (hsplit : Z (family P) v = Z (family P) u ⊔ Z (family P) a)
    (hdis : Disjoint (Z (family P) u) (Z (family P) a))
    (hR : ⁅Z (family P) v,Z (family P) w⁆ = Z (family P) u)
    (huc : Z (family P) w ≤ centralizer (Z (family P) u : Set G))
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥) :
    ∃ g ∈ Z (family P) w, g • a ≠ a := by
  classical
  let := finite_endpoints h
  by_contra hn
  push Not at hn
  have hfix : Z (family P) w ≤ stabilizer (family P) a := hn
  have hnorm : Z (family P) w ≤ normalizer (Z (family P) a : Set G) :=
    hfix.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _))
  have hcomm : ⁅Z (family P) a,Z (family P) w⁆ = ⊥ := by
    apply bot_unique
    rw [←(disjoint_iff.mp hdis)]
    apply le_inf
    · exact (commutator_mono (hsplit ▸ le_sup_right) le_rfl).trans hR.le
    · exact le_normalizer_iff_commutator_le_left.mp hnorm
  apply hne
  rw [commutator_eq_bot_iff_le_centralizer,hsplit]
  exact sup_le (le_centralizer_iff.mp huc)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)

theorem graph_core_and_mover_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v a : Vertex (family P)} (ha : (graph (family P)).Adj v a)
    (c : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) a))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    (hnat : HasNaturalCenter c.Pstar (Z (family P) v) (Q (family P) v))
    (hob : ¬ stabilizer (family P) a ≤ normalizer
      ((Q (family P) v ⊓ Q (family P) a : Subgroup G) : Set G))
    (A : Subgroup G) (hAv : A ≤ stabilizer (family P) v)
    (hm : ∃ g ∈ A, g • a ≠ a)
    {x : Vertex (family P)} (hx : (graph (family P)).Adj v x) :
    ∃ g ∈ Q (family P) a ⊔ A, g • a = x := by
  classical
  by_cases hxa : x = a
  · exact ⟨1,one_mem _,by simp [hxa]⟩
  obtain ⟨g,hg,hga⟩ := hm
  have hga' : (graph (family P)).Adj v (g • a) := by
    have he := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr ha
    change (graph (family P)).Adj (g • v) (g • a) at he
    rwa [show g • v = v from hAv hg] at he
  obtain ⟨q,hq,hqx⟩ := graph_natural_opposite_core_transitive h hB ha c ho hnat hob
    hga' hx hga hxa
  exact ⟨q*g,mul_mem (mem_sup_left hq) (mem_sup_right hg),by rwa [mul_smul]⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
