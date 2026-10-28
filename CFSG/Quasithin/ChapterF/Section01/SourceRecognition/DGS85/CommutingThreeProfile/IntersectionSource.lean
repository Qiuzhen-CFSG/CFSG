module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceLayers

/-!
# The middle intersection on the actual reduced source graph

The original starred endpoint acts transitively on the neighbors of its
base vertex: factor an element of the full reduced endpoint as a starred
element times an element of the whole reduced Borel. The latter fixes the
opposite base vertex. This discharges local transitivity in the geometric
intersection theorem, without assuming a prescribed permutation action.

The final application places H = V_x intersect V_y in the actual radius-three
kernel and maps H into the original parabolic two-core. H contains the
nonzero original graph center Z_m, is elementary abelian, and is normal
relative to both the reduced and original starred endpoints. All maps are
the original subtype inclusions; the original S is retained.

Source: DGS85 (12.3)(b), pp.179--180, and the geometric intersection in
(12.9)(c3), p.188; Aschbacher--Smith F.1.9. The Chapter 6 Sylow assertion,
common Sylows, Chapter 8 center and commutator properties, and b = 3 remain
explicit. The three-core generation identity displayed at the start of
p.180 also remains explicit: its source derivation must still be assembled
in this theorem family. Neither full (12.3) nor (12.9) is asserted here.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Reduction
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem star_transitive_from_base (h : HypothesisF11 L S) (i : Bool)
    {z : Vertex (reducedFamily L S)}
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z) :
    ∃ a ∈ star L S i, a • base (reducedFamily L S) (!i) = z := by
  let F := reducedFamily L S
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g, hg, hgz⟩ := locally_transitive F hadj hz
  have hgP : (g : G) ∈ P₀ L S (if i then 1 else 0) := by
    rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base] at hg
    cases i <;> exact hg
  have hp := P₀_set_product h (if i then 1 else 0)
  have hgSet : (g : G) ∈ (P₀ L S (if i then 1 else 0) : Set G) := hgP
  rw [hp] at hgSet
  obtain ⟨a, ha, c, hc, hac⟩ := hgSet
  have hcG : c ∈ G₀ L S := endpoint_le_completion (L := L) (S := S) 0
    ((show B₀ L S ≤ P₀ L S 0 from le_sup_right) hc)
  let a₀ : G₀ L S := ⟨a, star_le_completion (if i then 1 else 0) ha⟩
  let c₀ : G₀ L S := ⟨c, hcG⟩
  have hcc : c₀ • base F (!i) = base F (!i) := by
    change c₀ ∈ stabilizer F (base F (!i))
    rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
    cases i
    · exact (show B₀ L S ≤ P₀ L S 1 from le_sup_right) hc
    · exact (show B₀ L S ≤ P₀ L S 0 from le_sup_right) hc
  have he : a₀ * c₀ = g := Subtype.ext hac
  refine ⟨a₀, ha, ?_⟩
  rw [← he, mul_smul, hcc] at hgz
  exact hgz

/-- The full-Borel product proves local transitivity of the literal starred endpoint. -/
theorem star_locally_transitive (h : HypothesisF11 L S) (i : Bool)
    {x z : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z) :
    ∃ a ∈ star L S i, a • x = z := by
  obtain ⟨a, ha, hax⟩ := star_transitive_from_base h i hx
  obtain ⟨c, hc, hcz⟩ := star_transitive_from_base h i hz
  refine ⟨c * a⁻¹, (star L S i).mul_mem hc ((star L S i).inv_mem ha), ?_⟩
  rw [← hax, mul_smul, inv_smul_smul, hcz]

/-- Apply the intersection argument with actual reduced graph kernels and retain
relative normality and core containment in the original starred/parabolic groups. -/
theorem source_intersection_third_kernel (h : HypothesisF11 L S)
    (hSyl : ∀ v, ∃ T : Sylow 2 (U (reducedFamily L S) v),
      (T : Subgroup (U (reducedFamily L S) v)).map (U (reducedFamily L S) v).subtype =
        Q (reducedFamily L S) v)
    (hb : b (reducedFamily L S) = 3) (i : Bool)
    {x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) i))
    (hy : (graph (reducedFamily L S)).Adj y (base (reducedFamily L S) i))
    (Tx Ty : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)))
    (hTx : (Tx : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hTy : (Ty : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) y ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hcx : Z (reducedFamily L S) x ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hcy : Z (reducedFamily L S) y ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) y 1, Q (reducedFamily L S) y⁆ ≤ Z (reducedFamily L S) y)
    (hgen : star L S i = (Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) y) ⊔
      Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let H := V F x 1 ⊓ V F y 1
    (H.subgroupOf (star L S i)).Normal ∧
      ((H.map (G₀ L S).subtype).subgroupOf
        (starredParabolic L S (if i then 1 else 0))).Normal ∧
      IsElementaryAbelian 2 H ∧ Z F (base F i) ≤ H ∧ H ≠ ⊥ ∧
      H ≤ ballKernel F (base F i) 3 ∧
      H.map (G₀ L S).subtype ≤ (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
  dsimp only
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hr := intersection_third_kernel F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) hSyl
    (fun v => (source_Z_Q_U (reduced_triple h) v).2) hb hx hy Tx Ty hTx hTy hcx hcy
    hcommx hcommy (star L S i) hgen
    (fun z hz => star_locally_transitive h i hx.symm hz)
  have hzH : Z F (base F i) ≤ V F x 1 ⊓ V F y 1 := le_inf
    (le_iSup_of_le (base F i) (le_iSup_of_le
      ((mem_ball_one F x (base F i)).mpr (Or.inl hx)) le_rfl))
    (le_iSup_of_le (base F i) (le_iSup_of_le
      ((mem_ball_one F y (base F i)).mpr (Or.inl hy)) le_rfl))
  have hnon : V F x 1 ⊓ V F y 1 ≠ ⊥ := by
    intro he
    exact base_Z_ne_bot (reduced_triple h) i (bot_unique (hzH.trans he.le))
  have hn : star L S i ≤ normalizer ((V F x 1 ⊓ V F y 1 : Subgroup (G₀ L S)) : Set (G₀ L S)) :=
    (normal_subgroupOf_iff_le_normalizer
      (hr.2.1.trans (hgen ▸ le_sup_right))).mp hr.1
  have hnmap := (map_mono (f := (G₀ L S).subtype) hn).trans
    ((V F x 1 ⊓ V F y 1 : Subgroup (G₀ L S)).le_normalizer_map (G₀ L S).subtype)
  change ((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S) |>.map
    (G₀ L S).subtype) ≤ _ at hnmap
  rw [map_subgroupOf_eq_of_le (star_le_completion _)] at hnmap
  refine ⟨hr.1, normal_subgroupOf_of_le_normalizer hnmap,
    hr.2.2.2, hzH, hnon, hr.2.2.1, ?_⟩
  have hmap := map_mono (f := (G₀ L S).subtype) hr.2.1
  rw [← star_core h i, ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
    2 _ (G₀ L S).subtype_injective] at hmap
  change _ ≤ ((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S) |>.map
    (G₀ L S).subtype).pCoreIn 2 at hmap
  rw [map_subgroupOf_eq_of_le (star_le_completion _)] at hmap
  exact hmap.trans_eq (h.starredParabolic_same_core _)

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
