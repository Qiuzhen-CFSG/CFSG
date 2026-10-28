module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Graph
public import Theory.GroupTheory.SylowCommutatorCore

/-!
# Short center spans in the commuting critical branch

The two-orbit critical minimum puts short-distance centers in the full local
kernel U. Source 6.2(d), stated with an actual Sylow embedding, then puts them
in Q. Centrality in Q makes short-ball spans abelian. The closed radius-one
span includes its center; a nonzero displacement therefore detects a moving
neighbor. On a critical path, the preceding core escapes the final core, and
the radius-one spans act quadratically on one another once b is at least three.

Source: DGS, *Groups and Graphs* (1985), 8.0 and 8.1(c)--(e), pp.132--133.
The parity argument proving the required lower bound is in `Parity`.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

theorem Z_neighbor_le_V {v w : Vertex F} (h : (graph F).Adj v w) :
    Z F w ≤ V F v 1 :=
  le_iSup_of_le w (le_iSup_of_le ((mem_ball_one F v w).mpr (Or.inl h)) le_rfl)

/-- The closed ball has a separate center seed. -/
theorem V_one_eq_sup_neighbors (v : Vertex F) :
    V F v 1 = Z F v ⊔ ⨆ w : (graph F).neighborSet v, Z F w.val := by
  apply le_antisymm
  · apply iSup_le
    intro w
    apply iSup_le
    intro hw
    rcases (mem_ball_one F v w).mp hw with hw | rfl
    · exact (le_iSup (fun w : (graph F).neighborSet v => Z F w.val) ⟨w, hw⟩).trans
        le_sup_right
    · exact le_sup_left
  · exact sup_le (Z_le_V F v 1) (iSup_le fun w => Z_neighbor_le_V F w.property)

theorem stabilizer_normalizes_Q (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) :=
  (stabilizer F v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F v)))

theorem stabilizer_normalizes_Z [∀ i, Finite (F i)] (v : Vertex F) :
    stabilizer F v ≤ normalizer (Z F v : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F v)).mp (Z_normal F v)

theorem stabilizer_normalizes_V [∀ i, Finite (F i)] (v : Vertex F) (n : ℕ) :
    stabilizer F v ≤ normalizer (V F v n : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (V F v n).map (MulAut.conj g).toMonoidHom = V F v n
  rw [← V_translate F g v n]
  exact congrArg (fun w => V F w n) hg

theorem V_le_stabilizer_of_dist_add_le_b (hgen : F false ⊔ F true = ⊤)
    (v w : Vertex F) (n : ℕ) (hd : (graph F).dist v w + n ≤ b F) :
    V F v n ≤ stabilizer F w := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply Z_le_stabilizer_of_dist_le_b F hgen
  have hx' := (mem_ball_iff F hgen v x n).mp hx
  have ht := (connected F hgen).dist_triangle (u := x) (v := v) (w := w)
  rw [SimpleGraph.dist_comm (u := x) (v := v)] at ht
  omega

/-- The exact earlier-source 6.2(d) input identifies a Sylow of U with Q;
it does not identify U and Q. -/
theorem pSubgroup_le_Q_of_le_U (w : Vertex F) (A : Subgroup G)
    (hA : IsPGroup 2 A) (hAU : A ≤ U F w)
    (hSyl : ∃ T : Sylow 2 (U F w), (T : Subgroup (U F w)).map (U F w).subtype = Q F w) :
    A ≤ Q F w := by
  obtain ⟨T, hT⟩ := hSyl
  exact le_sylow_image_of_normalizes (U F w) T hT hA hAU
    (hAU.trans ((U_le_stabilizer F w).trans (stabilizer_normalizes_Q F w)))

theorem Z_le_Q_of_dist_lt_b
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (v w : Vertex F) (hd : (graph F).dist v w < b F)
    (hSyl : ∃ T : Sylow 2 (U F w), (T : Subgroup (U F w)).map (U F w).subtype = Q F w) :
    Z F v ≤ Q F w := by
  apply pSubgroup_le_Q_of_le_U F w (Z F v) _ (Z_le_U_of_dist_lt_b F v w hd) hSyl
  exact (isPGroup_pCoreIn 2 (stabilizer F v)).to_le ((hZ v).trans (map_subtype_le _))

theorem Z_centralizes_Q (v : Vertex F) (hZ : Z F v ≤ omegaCenterIn (Q F v)) :
    Z F v ≤ centralizer (Q F v : Set G) :=
  fun _ hx => ((mem_omegaCenterIn_iff _ _).mp (hZ hx)).2.1

theorem V_le_Q_of_dist_add_lt_b (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (v w : Vertex F) (n : ℕ) (hd : (graph F).dist v w + n < b F)
    (hSyl : ∃ T : Sylow 2 (U F w), (T : Subgroup (U F w)).map (U F w).subtype = Q F w) :
    V F v n ≤ Q F w := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply Z_le_Q_of_dist_lt_b F hZ x w _ hSyl
  have hx' := (mem_ball_iff F hgen v x n).mp hx
  have ht := (connected F hgen).dist_triangle (u := x) (v := v) (w := w)
  rw [SimpleGraph.dist_comm (u := x) (v := v)] at ht
  omega

/-- Short-ball center spans are abelian, using the global two-orbit minimum. -/
theorem V_isMulCommutative_of_two_mul_lt_b (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ w, ∃ T : Sylow 2 (U F w),
      (T : Subgroup (U F w)).map (U F w).subtype = Q F w)
    (v : Vertex F) (n : ℕ) (hn : 2 * n < b F) : IsMulCommutative (V F v n) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply le_centralizer_iff.mpr
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hxy : (graph F).dist y x < b F := by
    have hx' := (mem_ball_iff F hgen v x n).mp hx
    have hy' := (mem_ball_iff F hgen v y n).mp hy
    have ht := (connected F hgen).dist_triangle (u := y) (v := v) (w := x)
    rw [SimpleGraph.dist_comm (u := y) (v := v)] at ht
    omega
  exact (Z_le_Q_of_dist_lt_b F hZ y x hxy (hSyl x)).trans
    (le_centralizer_iff.mp (Z_centralizes_Q F x (hZ x)))

/-- Source 8.0's nontrivial H detects a moving neighbor. The center seed
cannot account for nontriviality, since A lies in Q at the center. -/
theorem exists_moving_neighbor
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v)) (beta a' : Vertex F)
    (hne : ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ ≠ ⊥) :
    ∃ w : (graph F).neighborSet a',
      ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ ∧ ¬ V F beta 1 ⊓ Q F a' ≤ Q F w.val := by
  have he : ∃ w : (graph F).neighborSet a', ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ := by
    by_contra! hall
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    rw [V_one_eq_sup_neighbors]
    apply sup_le
    · exact (Z_centralizes_Q F a' (hZ a')).trans (centralizer_le inf_le_right)
    · apply iSup_le
      intro w
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hall w))
  obtain ⟨w, hw⟩ := he
  refine ⟨w, hw, ?_⟩
  intro hQ
  apply hw
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact hQ.trans (le_centralizer_iff.mp (Z_centralizes_Q F w.val (hZ w.val)))

/-- At the distance occurring in 8.1(e), the two actual radius-one spans
normalize one another. This is independent of the commuting-center branch. -/
theorem radius_one_mutual_normalization [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤) (v w : Vertex F)
    (hd : (graph F).dist v w + 1 ≤ b F) :
    V F v 1 ≤ normalizer (V F w 1 : Set G) ∧
      V F w 1 ≤ normalizer (V F v 1 : Set G) := by
  refine ⟨(V_le_stabilizer_of_dist_add_le_b F hgen v w 1 hd).trans
    (stabilizer_normalizes_V F w 1), ?_⟩
  apply (V_le_stabilizer_of_dist_add_le_b F hgen w v 1 _).trans
    (stabilizer_normalizes_V F v 1)
  rwa [SimpleGraph.dist_comm]

/-- The actual subgroup form of mutual quadratic action in 8.1(e). -/
theorem radius_one_mutual_quadratic [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ w, ∃ T : Sylow 2 (U F w),
      (T : Subgroup (U F w)).map (U F w).subtype = Q F w)
    (v w : Vertex F) (hd : (graph F).dist v w + 1 ≤ b F) (hb : 3 ≤ b F) :
    ⁅⁅V F v 1, V F w 1⁆, V F v 1⁆ = ⊥ ∧
      ⁅⁅V F v 1, V F w 1⁆, V F w 1⁆ = ⊥ := by
  let := V_isMulCommutative_of_two_mul_lt_b F hgen hZ hSyl v 1 (by omega)
  let := V_isMulCommutative_of_two_mul_lt_b F hgen hZ hSyl w 1 (by omega)
  obtain ⟨hvw, hwv⟩ := radius_one_mutual_normalization F hgen v w hd
  exact ⟨commutator_eq_bot_iff_le_centralizer.mpr
      ((le_normalizer_iff_commutator_le_left.mp hwv).trans (le_centralizer _)),
    commutator_eq_bot_iff_le_centralizer.mpr
      ((le_normalizer_iff_commutator_le_right.mp hvw).trans (le_centralizer _))⟩

/-- Source 8.1(c)'s nonzero commutator follows from the actual nonzero H. -/
theorem radius_one_commutator_ne_bot (beta a' : Vertex F)
    (hne : ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆ ≠ ⊥) :
    ⁅V F beta 1, V F a' 1⁆ ≠ ⊥ := by
  intro h
  exact hne (eq_bot_iff.mpr ((commutator_mono inf_le_left le_rfl).trans h.le))

/-- Each endpoint core lies in every actual Sylow of its incident edge. -/
theorem Q_le_edge_sylow (hQU : ∀ v, Q F v ≤ U F v)
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    (T : Sylow 2 ↥(stabilizer F v ⊓ stabilizer F w : Subgroup G)) :
    Q F v ≤ (T : Subgroup ↥(stabilizer F v ⊓ stabilizer F w : Subgroup G)).map
      (stabilizer F v ⊓ stabilizer F w).subtype := by
  apply (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (stabilizer F v))
    (le_inf (Q_le_stabilizer F v)
      ((hQU v).trans ((ballKernel_one_le_edge F hvw).trans inf_le_right)))
    (inf_le_left.trans (stabilizer_normalizes_Q F v))).trans
      (pCoreIn_le_sylow _ T)

/-- The previous core on the chosen critical path escapes Q at the end,
as asserted in 8.1(d). The proof uses the global minimum, not an orbit minimum. -/
theorem exists_previous_core_escape (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hQU : ∀ v, Q F v ≤ U F v)
    (hSyl : ∀ w, ∃ T : Sylow 2 (U F w),
      (T : Subgroup (U F w)).map (U F w).subtype = Q F w)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) :
    ∃ prev : Vertex F, (graph F).Adj a' prev ∧
      (graph F).dist beta prev + 1 = (graph F).dist beta a' ∧
      V F beta 1 ≤ Q F prev ∧ ¬ Q F prev ≤ Q F a' := by
  have hne : beta ≠ a' := by
    intro he
    subst a'
    simp only [SimpleGraph.dist_self] at hd
    omega
  obtain ⟨prev, hp, hdprev⟩ := exists_predecessor F hgen beta a' hne
  have hVQ : V F beta 1 ≤ Q F prev :=
    V_le_Q_of_dist_add_lt_b F hgen hZ beta prev 1 (by omega) (hSyl prev)
  refine ⟨prev, hp, hdprev, hVQ, ?_⟩
  intro hQ
  exact hc.2 ((Z_neighbor_le_V F hab.symm).trans (hVQ.trans (hQ.trans (hQU a'))))


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
