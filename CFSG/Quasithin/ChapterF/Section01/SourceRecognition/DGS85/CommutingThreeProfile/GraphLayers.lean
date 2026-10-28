module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Graph
public import Theory.ElementaryAbelian.CommutingFamily

/-!
# The geometric center layer at critical distance three

The actual span V_delta^(i) fixes the radius-j ball when i+j <= b. The
source 6.2(d) input says exactly that Q_delta is a Sylow two-subgroup of
the full local kernel U_delta; it does not equate Q and U. Consequently
centers at distance less than b lie in each other's two-cores. For b > 2,
the generators of V_delta commute, so V_delta is elementary abelian and
normal in the vertex group, hence lies in Q_delta.

At the first neighbor of an actual distance-three critical pair, Z_beta
is a proper subgroup of V_beta, and V_beta fixes the radius-two ball.
These are the literal elementary section and geometric placements used
in DGS85 (12.3)--(12.6), printed pp.179--183. No Suzuki marking, upper
bound, or Chapter 12 conclusion is assumed. The separate Chapter 6 owner
supplies 6.2(d), and the Chapter 8 owner supplies b=3.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Every center generator fixes the specified ball by the global critical minimum. -/
theorem V_le_ballKernel (hgen : F false ⊔ F true = ⊤)
    (v : Vertex F) {i j : ℕ} (hij : i + j ≤ b F) :
    V F v i ≤ ballKernel F v j := by
  apply iSup_le
  intro w
  apply iSup_le
  intro hw x hx u hu
  have hwu : (graph F).dist w u ≤ b F := by
    have hw' := (mem_ball_iff F hgen v w i).mp hw
    have hu' := (mem_ball_iff F hgen v u j).mp hu
    have ht := (connected F hgen).dist_triangle (u := w) (v := v) (w := u)
    rw [SimpleGraph.dist_comm (u := w) (v := v)] at ht
    omega
  exact Z_le_stabilizer_of_dist_le_b F hgen w u hwu hx

/-- Normality is relative to the actual vertex stabilizer. -/
theorem stabilizer_normalizes_V [∀ i, Finite (F i)] (v : Vertex F) (n : ℕ) :
    stabilizer F v ≤ normalizer (V F v n : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (V F v n).map (MulAut.conj g).toMonoidHom = V F v n
  rw [← V_translate F]
  change g • v = v at hg
  rw [hg]

/-- The actual source centers inherit exponent two and commutativity. -/
theorem Z_elementary (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v)) (v : Vertex F) :
    IsElementaryAbelian 2 (Z F v) := IsElementaryAbelian.of_le (hZ v)

/-- Source 6.2(d) upgrades the strict-distance kernel containment to core containment. -/
theorem Z_le_Q_of_dist_lt_b
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (v w : Vertex F) (hd : (graph F).dist v w < b F) : Z F v ≤ Q F w := by
  have hZU := Z_le_U_of_dist_lt_b F v w hd
  obtain ⟨T, hT⟩ := hSyl w
  have hn : ((Q F w).subgroupOf (U F w)).Normal := by
    change (((stabilizer F w).pCoreIn 2).subgroupOf (U F w)).Normal
    apply normal_subgroupOf_of_le_normalizer
    exact (U_le_stabilizer F w).trans ((stabilizer F w).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F w))))
  have hTU : (T : Subgroup (U F w)) = (Q F w).subgroupOf (U F w) := by
    apply map_injective (U F w).subtype_injective
    rw [map_subgroupOf_eq_of_le (hT ▸ map_subtype_le _), hT]
  let : (T : Subgroup (U F w)).Normal := hTU ▸ hn
  let : IsElementaryAbelian 2 (Z F v) := Z_elementary F hZ v
  have hp := (IsElementaryAbelian.isPGroup 2 (Z F v)).comap_subtype (K := U F w)
  have hle : (Z F v).subgroupOf (U F w) ≤ T := by
    have hs := T.is_maximal' (T.isPGroup'.to_sup_of_normal_left hp) le_sup_left
    exact le_sup_right.trans hs.le
  have hm := map_mono (f := (U F w).subtype) hle
  rwa [map_subgroupOf_eq_of_le hZU, hT] at hm

/-- Neighboring generators are at distance at most two and centralize one another. -/
theorem V_elementary
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (hb : 2 < b F) (v : Vertex F) : IsElementaryAbelian 2 (V F v 1) := by
  let E : ball F v 1 → Subgroup G := fun w => Z F w.val
  have heq : V F v 1 = ⨆ w, E w := by
    simp only [V, E, iSup_subtype]
  rw [heq]
  let : ∀ w, IsElementaryAbelian 2 (E w) := fun w => Z_elementary F hZ w.val
  apply IsElementaryAbelian.iSup_of_le_centralizer
  intro w u
  have hd : (graph F).dist w.val u.val < b F := by
    have hw := (mem_ball_iff F hgen v w.val 1).mp w.property
    have hu := (mem_ball_iff F hgen v u.val 1).mp u.property
    have ht := (connected F hgen).dist_triangle (u := w.val) (v := v) (w := u.val)
    rw [SimpleGraph.dist_comm (u := w.val) (v := v)] at ht
    omega
  apply le_centralizer_iff.mp
  exact (hZ u.val).trans (fun x hx => centralizer_le
    (Z_le_Q_of_dist_lt_b F hZ hSyl w.val u.val hd)
    ((mem_omegaCenterIn_iff _ _).mp hx).2.1)

/-- The elementary center span is normal in the vertex group, so lies in its two-core. -/
theorem V_le_Q [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (hb : 2 < b F) (v : Vertex F) : V F v 1 ≤ Q F v := by
  let : IsElementaryAbelian 2 (V F v 1) := V_elementary F hgen hZ hSyl hb v
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (V F v 1))
    ?_ (stabilizer_normalizes_V F v 1)
  exact (V_le_ballKernel F hgen v (i := 1) (j := 0) (by omega)).trans
    (ballKernel_le_stabilizer F v 0)

/-- A critical escape forces a genuine nonzero center quotient at the intervening vertex. -/
theorem critical_neighbor_span_not_le_center {a a' beta : Vertex F}
    (hc : IsCriticalPair F a a') (ha : (graph F).Adj beta a)
    (hd : (graph F).dist beta a' < b F) : ¬ V F beta 1 ≤ Z F beta := by
  intro he
  have hseed : Z F a ≤ V F beta 1 :=
    le_iSup_of_le a (le_iSup_of_le ((mem_ball_one F beta a).mpr (Or.inl ha)) le_rfl)
  exact hc.2 (hseed.trans (he.trans (Z_le_U_of_dist_lt_b F beta a' hd)))

/-- The first neighbor of a distance-three critical pair has a proper center layer in its radius-two kernel. -/
theorem critical_three_neighbor (hgen : F false ⊔ F true = ⊤)
    (hb : b F = 3) {a a' : Vertex F} (hc : IsCriticalPair F a a') :
    ∃ beta, (graph F).Adj a beta ∧ (graph F).dist beta a' = 2 ∧
      Z F beta < V F beta 1 ∧ V F beta 1 ≤ ballKernel F beta 2 := by
  have hne : a' ≠ a := by
    intro he
    have h := hc.1
    rw [he, SimpleGraph.dist_self, hb] at h
    omega
  obtain ⟨beta, ha, hd⟩ := exists_predecessor F hgen a' a hne
  rw [SimpleGraph.dist_comm (u := a') (v := a), hc.1, hb,
    SimpleGraph.dist_comm (u := a') (v := beta)] at hd
  have hd' : (graph F).dist beta a' = 2 := by omega
  refine ⟨beta, ha, hd', ?_, V_le_ballKernel F hgen beta (by omega)⟩
  exact lt_of_le_not_ge (Z_le_V F beta 1)
    (critical_neighbor_span_not_le_center F hc ha.symm (by omega))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
