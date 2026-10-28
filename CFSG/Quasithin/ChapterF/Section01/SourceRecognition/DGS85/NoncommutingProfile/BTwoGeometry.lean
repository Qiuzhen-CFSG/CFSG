module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.GraphRadius
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The adjacent core intersection in the noncentral b=2 branch

The source span Q_v=Z_w Z_t D_v and the literal D_v=Q_w∩Q_t=Z_v
identify Q_v∩Q_w with Z_v Z_w. Relative normalization and the short
critical distance then put [Z_t,Q_w,Z_t] in Z_w. This proves the
quadratic bound needed on Q_w/Z_w from the paired subgroup geometry.

Only the core span and D identity remain explicit. The proof uses the
actual two-cores and the Sylow property in the full permutation kernels;
it does not identify those kernels with the cores or assume a tree.
Source: DGS, *Groups and Graphs* (1985), 10.4 and 10.6, pp.155--157.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

private theorem source_center_core (h : LocallyRankOneTriple P B) (v : Vertex F) :
    Z F v ≤ Q F v := by
  intro z hz
  exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hz)).1

private theorem source_core_normalizer (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) :=
  (stabilizer F v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The source core span and literal D=Z calculate the adjacent core
intersection, without identifying Q with the full permutation kernel. -/
theorem bTwo_adjacent_core_intersection (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x)) (hb : b F = 2)
    {t v w : Vertex F} (htv : (graph F).Adj t v) (hvw : (graph F).Adj v w)
    (hc : IsCriticalPair F w t)
    (hspan : Q F v = (Z F w ⊔ Z F t) ⊔ D F w t)
    (hD : D F w t = Z F v) :
    Q F v ⊓ Q F w = Z F v ⊔ Z F w := by
  let := finite_endpoints h
  have hZWv : Z F w ≤ Q F v := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw.symm,hb]; decide)
  have hZVw : Z F v ≤ Q F w := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw,hb]; decide)
  have hZVt : Z F v ≤ centralizer (Z F t : Set G) := graph_centers_commute_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv.symm,hb]; decide)
  have hnormal : Z F v ⊔ Z F w ≤ normalizer (Z F t : Set G) := by
    apply sup_le (hZVt.trans (Subgroup.centralizer_le_normalizer _))
    exact le_normalizer_iff_commutator_le_right.mpr
      ((criticalPair_centers F h.generate hc).2.trans inf_le_right)
  have hfactor : Q F v = (Z F v ⊔ Z F w) ⊔ Z F t := by
    rw [hspan,hD]
    ac_rfl
  apply le_antisymm
  · rintro x ⟨hx,hxw⟩
    have hxp : x ∈ ((Z F v ⊔ Z F w : Subgroup G) : Set G) * (Z F t : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hnormal,←hfactor]
      exact hx
    obtain ⟨a,ha,c,hc,rfl⟩ := hxp
    have haQ : a ∈ Q F w := (sup_le hZVw (source_center_core h w)) ha
    have hcQ : c ∈ Q F w := by
      simpa only [inv_mul_cancel_left] using (Q F w).mul_mem ((Q F w).inv_mem haQ) hxw
    have hcZ : c ∈ Z F v := hD ▸ (show c ∈ D F w t from ⟨hcQ,source_center_core h t hc⟩)
    exact (Z F v ⊔ Z F w).mul_mem ha ((le_sup_left : Z F v ≤ Z F v ⊔ Z F w) hcZ)
  · exact sup_le (le_inf (source_center_core h v) hZVw)
      (le_inf hZWv (source_center_core h w))

/-- The same adjacent-core calculation proves the double commutator bound
used in 10.6. It is not an extra quotient-action assumption. -/
theorem bTwo_quadratic_core_commutator (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x)) (hb : b F = 2)
    {t v w : Vertex F} (htv : (graph F).Adj t v) (hvw : (graph F).Adj v w)
    (hc : IsCriticalPair F w t)
    (hspan : Q F v = (Z F w ⊔ Z F t) ⊔ D F w t)
    (hD : D F w t = Z F v) : ⁅Z F t,⁅Z F t,Q F w⁆⁆ ≤ Z F w := by
  let := finite_endpoints h
  have hi := bTwo_adjacent_core_intersection h hS hb htv hvw hc hspan hD
  have hTv : Z F t ≤ Q F v := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv,hb]; decide)
  have hWv : Q F w ≤ stabilizer F v :=
    (source_Z_Q_U h w).2.trans ((ballKernel_one_le_edge F hvw.symm).trans inf_le_right)
  have hVw : Q F v ≤ stabilizer F w :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F hvw).trans inf_le_right)
  have hTc := (criticalPair_centers F h.generate hc).1
  have hcomm : ⁅Z F t,Q F w⁆ ≤ Z F v ⊔ Z F w := by
    apply le_trans _ hi.le
    apply le_inf
    · exact (commutator_mono hTv le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hWv.trans (source_core_normalizer v)))
    · exact le_normalizer_iff_commutator_le_right.mp (hTc.trans (source_core_normalizer w))
  apply (commutator_mono le_rfl hcomm).trans
  rw [commutator_comm]
  apply commutator_sup_le_of_relative_normal (Q F v) (Z F v) (Z F w) (Z F t) (Z F w)
  · exact hVw.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F w)).mp (Z_normal F w))
  · exact source_center_core h v
  · exact graph_Z_le_Q_of_short h hS
      (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw.symm,hb]; decide)
  · have he : ⁅Z F v,Z F t⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (graph_centers_commute_of_short h hS
        (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv.symm,hb]; decide))
    exact he.le.trans bot_le
  · exact (criticalPair_centers F h.generate hc).2.trans inf_le_left
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
