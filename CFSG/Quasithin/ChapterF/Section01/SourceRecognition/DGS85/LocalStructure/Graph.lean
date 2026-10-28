module
public import Theory.GroupTheory.AmalgamGraph.LocalAction
public import Theory.GroupTheory.AmalgamGraph.SylowCenterSpan

/-!
# The shared DGS graph notation and the two-orbit critical minimum

Q is the embedded intrinsic two-core; U is the kernel on the closed
radius-one neighborhood. Z joins the omega-centers of all actual Sylows,
and V joins Z over the whole closed ball, including its center. Escape is
from U. The global escape set is proved to be the union of the two endpoint
escape sets, so its attained minimum is the minimum of both orbit minima.
Faithfulness and a nonzero Z guarantee an escape, without finite completion.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, pp.81--83. The coset conventions are the verified inverse bridge
in `RankTwoCosetGeometry`; no acyclicity is assumed here.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- DGS Q_delta is the intrinsic two-core, embedded in the acting group. -/
def Q (v : Vertex F) : Subgroup G := (stabilizer F v).pCoreIn 2
/-- DGS G_delta^(1), denoted U here, fixes the closed radius-one ball. -/
def U (v : Vertex F) : Subgroup G := ballKernel F v 1
/-- All actual Sylow-center images generate DGS Z_delta. -/
def Z (v : Vertex F) : Subgroup G := sylowCenterSpan (stabilizer F v)
/-- DGS V_delta^(i) includes the center vertex, and uses every vertex in the ball. -/
def V (v : Vertex F) (i : ℕ) : Subgroup G := ⨆ w ∈ ball F v i, Z F w
/-- Escape distances from one specified vertex, through the full local kernel. -/
def criticalDistancesAt (v : Vertex F) : Set ℕ :=
  {n | ∃ w : Vertex F, (graph F).dist v w = n ∧ ¬ Z F v ≤ U F w}
/-- Escape distances across both vertex orbits. -/
def criticalDistances : Set ℕ :=
  {n | ∃ v : Vertex F, n ∈ criticalDistancesAt F v}
/-- Source b_delta; attainment requires a nonempty escape set. -/
def bAt (v : Vertex F) : ℕ := sInf (criticalDistancesAt F v)
/-- Source b: the minimum across both vertex orbits, not just one endpoint. -/
def b : ℕ := sInf (criticalDistances F)
/-- A critical pair has the global minimum distance and an actual kernel escape. -/
def IsCriticalPair (v w : Vertex F) : Prop :=
  (graph F).dist v w = b F ∧ ¬ Z F v ≤ U F w

@[simp] theorem U_eq_localAction_kernel (v : Vertex F) :
    (U F v).subgroupOf (stabilizer F v) = (localAction F v).ker :=
  (localAction_ker F v).symm

theorem Q_le_stabilizer (v : Vertex F) : Q F v ≤ stabilizer F v := map_subtype_le _
theorem U_le_stabilizer (v : Vertex F) : U F v ≤ stabilizer F v :=
  ballKernel_le_stabilizer F v 1
theorem Z_le_stabilizer (v : Vertex F) : Z F v ≤ stabilizer F v :=
  sylowCenterSpan_le _
theorem Z_le_V (v : Vertex F) (i : ℕ) : Z F v ≤ V F v i :=
  le_iSup_of_le v (le_iSup_of_le (center_mem_ball F v i) le_rfl)

theorem V_mono (v : Vertex F) {i j : ℕ} (h : i ≤ j) : V F v i ≤ V F v j := by
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  exact le_iSup_of_le w (le_iSup_of_le (ball_mono F v h hw) le_rfl)

theorem V_eq_distance_span (hgen : F false ⊔ F true = ⊤) (v : Vertex F) (i : ℕ) :
    V F v i = ⨆ w : Vertex F, ⨆ (_ : (graph F).dist v w ≤ i), Z F w := by
  simp only [V, mem_ball_iff F hgen]

theorem Q_translate (g : G) (v : Vertex F) :
    Q F (g • v) = (Q F v).map (MulAut.conj g).toMonoidHom := by
  unfold Q
  rw [stabilizer_translate, Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj g).injective]

theorem U_translate (g : G) (v : Vertex F) :
    U F (g • v) = (U F v).map (MulAut.conj g).toMonoidHom :=
  ballKernel_translate F g v 1


theorem Z_translate [∀ i, Finite (F i)] (g : G) (v : Vertex F) :
    Z F (g • v) = (Z F v).map (MulAut.conj g).toMonoidHom := by
  unfold Z
  rw [stabilizer_translate, sylowCenterSpan_map]

theorem Z_normal [∀ i, Finite (F i)] (v : Vertex F) : ((Z F v).subgroupOf (stabilizer F v)).Normal :=
  sylowCenterSpan_normal _

theorem Z_le_coreOmega (v : Vertex F)
    (hc : centralizer (pCore 2 (stabilizer F v) : Set (stabilizer F v)) ≤
      pCore 2 (stabilizer F v)) :
    Z F v ≤ omegaCenterIn (Q F v) := sylowCenterSpan_le_coreOmega _ hc

theorem criticalDistancesAt_translate [∀ i, Finite (F i)] (g : G) (v : Vertex F) :
    criticalDistancesAt F (g • v) = criticalDistancesAt F v := by
  ext n
  constructor
  · rintro ⟨w, hw, hescape⟩
    refine ⟨g⁻¹ • w, ?_, ?_⟩
    · have hd := dist_smul F g v (g⁻¹ • w)
      simpa only [smul_inv_smul] using hd.symm
        |>.trans (by simpa only [smul_inv_smul] using hw)
    · intro h
      apply hescape
      have hm := map_mono (f := (MulAut.conj g).toMonoidHom) h
      rw [← Z_translate, ← U_translate, smul_inv_smul] at hm
      exact hm
  · rintro ⟨w, hw, hescape⟩
    refine ⟨g • w, (dist_smul F g v w).trans hw, ?_⟩
    intro h
    apply hescape
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
    rw [← Z_translate, ← U_translate, inv_smul_smul, inv_smul_smul] at hm
    exact hm

/-- The global escape set is precisely the union of the two endpoint escape sets. -/
theorem criticalDistances_eq_union [∀ i, Finite (F i)] : criticalDistances F =
    criticalDistancesAt F (base F false) ∪ criticalDistancesAt F (base F true) := by
  ext n
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
    rw [← hg, criticalDistancesAt_translate] at hv
    cases ht : v.type
    · exact Or.inl (by simpa only [ht] using hv)
    · exact Or.inr (by simpa only [ht] using hv)
  · rintro (h | h)
    · exact ⟨base F false, h⟩
    · exact ⟨base F true, h⟩

/-- Source b is the smaller of the two endpoint minima, once both exist. -/
theorem b_eq_min [∀ i, Finite (F i)] (h₀ : (criticalDistancesAt F (base F false)).Nonempty)
    (h₁ : (criticalDistancesAt F (base F true)).Nonempty) :
    b F = min (bAt F (base F false)) (bAt F (base F true)) := by
  have hb : (criticalDistances F).Nonempty := by
    rw [criticalDistances_eq_union]
    exact h₀.inl
  apply le_antisymm
  · apply le_min
    · exact Nat.sInf_le ⟨base F false, Nat.sInf_mem h₀⟩
    · exact Nat.sInf_le ⟨base F true, Nat.sInf_mem h₁⟩
  · have hm := Nat.sInf_mem hb
    change b F ∈ criticalDistances F at hm
    rw [criticalDistances_eq_union] at hm
    rcases hm with hm | hm
    · exact (min_le_left _ _).trans (Nat.sInf_le hm)
    · exact (min_le_right _ _).trans (Nat.sInf_le hm)

/-- Strictly shorter distances force containment in the full local kernel. -/
theorem Z_le_U_of_dist_lt_b (v w : Vertex F) (h : (graph F).dist v w < b F) :
    Z F v ≤ U F w := by
  by_contra he
  exact (not_le_of_gt h) (Nat.sInf_le ⟨v, w, rfl, he⟩)

/-- A nontrivial Sylow-center span in a faithful action necessarily escapes. -/
theorem criticalDistancesAt_nonempty [FaithfulSMul G (Vertex F)] (v : Vertex F)
    (hz : Z F v ≠ ⊥) : (criticalDistancesAt F v).Nonempty := by
  by_contra he
  apply hz
  apply eq_bot_iff.mpr
  intro g hg
  apply (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G (Vertex F)))
  intro w
  have hle : Z F v ≤ U F w := by
    by_contra hw
    exact he ⟨(graph F).dist v w, w, rfl, hw⟩
  exact U_le_stabilizer F w (hle hg)

/-- Nonempty escape distances supply an attained global critical pair. -/
theorem exists_criticalPair (h : (criticalDistances F).Nonempty) :
    ∃ v w : Vertex F, IsCriticalPair F v w := by
  obtain ⟨v, w, hd, he⟩ := Nat.sInf_mem h
  exact ⟨v, w, hd, he⟩

/-- All ball-center generators transport together under the original action. -/
theorem V_translate [∀ i, Finite (F i)] (g : G) (v : Vertex F) (i : ℕ) :
    V F (g • v) i = (V F v i).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · apply iSup_le
    intro w
    apply iSup_le
    intro hw
    have hw' : g⁻¹ • w ∈ ball F v i := by
      apply (smul_mem_ball F g v (g⁻¹ • w) i).mp
      simpa only [smul_inv_smul] using hw
    have he : Z F w = (Z F (g⁻¹ • w)).map (MulAut.conj g).toMonoidHom := by
      simpa only [smul_inv_smul] using Z_translate F g (g⁻¹ • w)
    rw [he]
    exact map_mono (le_iSup_of_le (g⁻¹ • w) (le_iSup_of_le hw' le_rfl))
  · rw [V, Subgroup.map_iSup]
    apply iSup_le
    intro w
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hw
    rw [← Z_translate]
    exact le_iSup_of_le (g • w) (le_iSup_of_le
      ((smul_mem_ball F g v w i).mpr hw) le_rfl)

/-- At distances at most b, each center lies in the other vertex stabilizer. -/
theorem Z_le_stabilizer_of_dist_le_b (hgen : F false ⊔ F true = ⊤)
    (v w : Vertex F) (hd : (graph F).dist v w ≤ b F) :
    Z F v ≤ stabilizer F w := by
  by_cases he : v = w
  · subst w; exact Z_le_stabilizer F v
  obtain ⟨x, hx, hdist⟩ := exists_predecessor F hgen v w he
  have hshort : (graph F).dist v x < b F := by omega
  exact (Z_le_U_of_dist_lt_b F v x hshort).trans
    ((ballKernel_one_le_edge F hx.symm).trans inf_le_right)

/-- Source 3.8(c): the literal critical centers normalize each other, and their
commutator is contained in both centers. -/
theorem criticalPair_centers [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤) {v w : Vertex F} (hc : IsCriticalPair F v w) :
    Z F w ≤ stabilizer F v ∧ ⁅Z F v, Z F w⁆ ≤ Z F v ⊓ Z F w := by
  have hvw := Z_le_stabilizer_of_dist_le_b F hgen v w hc.1.le
  have hwv : Z F w ≤ stabilizer F v := by
    apply Z_le_stabilizer_of_dist_le_b F hgen w v
    rw [SimpleGraph.dist_comm]
    exact hc.1.le
  have hn (x : Vertex F) : stabilizer F x ≤ normalizer (Z F x : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F x)).mp (Z_normal F x)
  exact ⟨hwv, le_inf (le_normalizer_iff_commutator_le_left.mp (hwv.trans (hn v)))
    (le_normalizer_iff_commutator_le_right.mp (hvw.trans (hn w)))⟩

end CFSG.Quasithin.ChapterF.Source.DGS85
