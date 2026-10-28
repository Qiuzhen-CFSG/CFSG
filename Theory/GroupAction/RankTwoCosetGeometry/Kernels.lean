module

public import Theory.GroupAction.RankTwoCosetGeometry.Distance
public import Theory.GroupTheory.FiniteSubgroupFiltration

/-!
# Pointwise ball kernels

The pointwise fixer of a ball is normal in its vertex stabilizer. Local
transitivity identifies the radius-one kernel with the normal core of any
incident edge stabilizer, taken inside that vertex stabilizer. Connectedness
identifies the intersection of all ball kernels with the global action kernel.

Finite vertex groups make each descending filtration stabilize. There are just
two vertex orbits, so trivial global kernel gives one positive radius valid
at every vertex, without requiring a finite ambient group.

Source: Aschbacher–Smith, F.7.3(6)–(8), printed pp.311–312. The group-theoretic
discharge of trivial global kernel in F.7.1 is deliberately a separate input.
-/

@[expose] public section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The pointwise stabilizer of the entire closed ball, including its center. -/
def ballKernel (v : Vertex F) (n : ℕ) : Subgroup G where
  carrier := {g | ∀ w ∈ ball F v n, g • w = w}
  one_mem' := by intro w _; exact one_smul G w
  mul_mem' := by intro g h hg hh w hw; rw [mul_smul, hh w hw, hg w hw]
  inv_mem' := by
    intro g hg w hw
    calc
      g⁻¹ • w = g⁻¹ • (g • w) := congrArg (g⁻¹ • ·) (hg w hw).symm
      _ = w := inv_smul_smul g w

@[simp] theorem mem_ballKernel (v : Vertex F) (n : ℕ) (g : G) :
    g ∈ ballKernel F v n ↔ ∀ w ∈ ball F v n, g • w = w := Iff.rfl

theorem ballKernel_le_stabilizer (v : Vertex F) (n : ℕ) :
    ballKernel F v n ≤ stabilizer F v := fun _ hg => hg v (center_mem_ball F v n)

@[simp] theorem ballKernel_zero (v : Vertex F) : ballKernel F v 0 = stabilizer F v := by
  apply le_antisymm (ballKernel_le_stabilizer F v 0)
  intro g hg w hw
  rw [(mem_ball_zero F v w).mp hw]
  exact hg

theorem ballKernel_antitone (v : Vertex F) : Antitone (ballKernel F v) := by
  intro m n h g hg w hw
  exact hg w (ball_mono F v h hw)

/-- Comparing kernels at adjacent centers is the geometric step in F.7.3(8). -/
theorem ballKernel_succ_le {v w : Vertex F} (h : (graph F).Adj v w) (n : ℕ) :
    ballKernel F v (n + 1) ≤ ballKernel F w n := by
  intro g hg z hz
  exact hg z (ball_subset_succ F h n hz)

/-- A kernel conjugates exactly with its center. -/
theorem conj_mem_ballKernel_iff (g x : G) (v : Vertex F) (n : ℕ) :
    g * x * g⁻¹ ∈ ballKernel F (g • v) n ↔ x ∈ ballKernel F v n := by
  constructor
  · intro h w hw
    have hf := h (g • w) ((smul_mem_ball F g v w n).mpr hw)
    have he : g • (x • w) = g • w := by simpa only [mul_smul, inv_smul_smul] using hf
    exact (MulAction.injective g) he
  · intro h w hw
    have hw' : g⁻¹ • w ∈ ball F v n :=
      (smul_mem_ball F g v (g⁻¹ • w) n).mp (by simpa only [smul_inv_smul] using hw)
    change (g * x * g⁻¹) • w = w
    rw [mul_smul, mul_smul, h _ hw', smul_inv_smul]

theorem ballKernel_translate (g : G) (v : Vertex F) (n : ℕ) :
    ballKernel F (g • v) n = (ballKernel F v n).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_equiv]
  have h := conj_mem_ballKernel_iff F g⁻¹ x (g • v) n
  simpa only [inv_inv, inv_smul_smul, MulAut.conj_symm_apply] using h.symm

/-- Normality is relative to the vertex stabilizer, not the whole ambient group. -/
instance ballKernel_normal (v : Vertex F) (n : ℕ) :
    ((ballKernel F v n).subgroupOf (stabilizer F v)).Normal where
  conj_mem x hx g := by
    change (g : G) * (x : G) * (g : G)⁻¹ ∈ ballKernel F v n
    have hg : (g : G) • v = v := g.property
    have h := (conj_mem_ballKernel_iff F (g : G) (x : G) v n).mpr hx
    rwa [hg] at h

/-- The ambient normalizer formulation of relative ball-kernel normality. -/
theorem stabilizer_le_normalizer_ballKernel (v : Vertex F) (n : ℕ) :
    stabilizer F v ≤ normalizer (ballKernel F v n : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (ballKernel_le_stabilizer F v n)).mp
    (ballKernel_normal F v n)

/-- Every radius-one kernel is contained in each incident edge stabilizer. -/
theorem ballKernel_one_le_edge {v w : Vertex F} (h : (graph F).Adj v w) :
    ballKernel F v 1 ≤ stabilizer F v ⊓ stabilizer F w := by
  intro g hg
  exact ⟨ballKernel_le_stabilizer F v 1 hg, hg w ((mem_ball_one F v w).mpr (Or.inl h))⟩

/-- The local kernel is the largest normal subgroup of the vertex stabilizer
contained in the incident edge stabilizer, with the relative ambient group explicit. -/
theorem ballKernel_one_eq_normalCore {v w : Vertex F} (h : (graph F).Adj v w) :
    (ballKernel F v 1).subgroupOf (stabilizer F v) =
      ((stabilizer F v ⊓ stabilizer F w).subgroupOf (stabilizer F v)).normalCore := by
  apply le_antisymm
  · apply normal_le_normalCore.mpr
    intro x hx
    exact ballKernel_one_le_edge F h hx
  · intro x hx z hz
    rcases (mem_ball_one F v z).mp hz with hz | rfl
    · obtain ⟨g, hg, rfl⟩ := locally_transitive F h hz
      have hc := hx (⟨g⁻¹, (stabilizer F v).inv_mem hg⟩ : stabilizer F v)
      change (g⁻¹ * (x : G) * (g⁻¹)⁻¹) ∈ stabilizer F v ⊓ stabilizer F w at hc
      have hf : (g⁻¹ * (x : G) * g) • w = w := by
        have hf' : (g⁻¹ * (x : G) * (g⁻¹)⁻¹) • w = w := hc.2
        simpa only [inv_inv] using hf'
      calc
        (x : G) • (g • w) = g • ((g⁻¹ * (x : G) * g) • w) := by
          simp only [mul_smul, smul_inv_smul]
        _ = g • w := congrArg (g • ·) hf
    · exact x.property

/-- The maximality clause in F.7.3(7), stated for arbitrary local normal subgroups. -/
theorem normal_le_ballKernel_one_iff {v w : Vertex F} (h : (graph F).Adj v w)
    (N : Subgroup (stabilizer F v)) [N.Normal] :
    N ≤ (ballKernel F v 1).subgroupOf (stabilizer F v) ↔
      N ≤ (stabilizer F v ⊓ stabilizer F w).subgroupOf (stabilizer F v) := by
  rw [ballKernel_one_eq_normalCore F h]
  exact normal_le_normalCore

/-- The local core mapped back to the acting group is the actual ball kernel.
This matches the ambient-subgroup convention of local-core algebra. -/
theorem ballKernel_one_eq_map_normalCore {v w : Vertex F} (h : (graph F).Adj v w) :
    ballKernel F v 1 =
      ((stabilizer F v ⊓ stabilizer F w).subgroupOf (stabilizer F v)).normalCore.map
        (stabilizer F v).subtype := by
  rw [← ballKernel_one_eq_normalCore F h,
    map_subgroupOf_eq_of_le (ballKernel_le_stabilizer F v 1)]

private theorem identified_local_kernel {v w : Vertex F} (h : (graph F).Adj v w)
    {H K : Subgroup G} (hv : stabilizer F v = H) (hw : stabilizer F w = K) :
    (ballKernel F v 1).subgroupOf H = ((H ⊓ K).subgroupOf H).normalCore := by
  subst H
  subst K
  exact ballKernel_one_eq_normalCore F h

/-- At a standard vertex, the source edge group is the intersection of the two groups. -/
theorem base_ballKernel_one (i : Bool) :
    (ballKernel F (base F i) 1).subgroupOf (F i) =
      ((F false ⊓ F true).subgroupOf (F i)).normalCore := by
  have h := identified_local_kernel F
    (v := base F i) (w := base F (!i))
    ⟨by change i ≠ !i; cases i <;> decide, incident_base F i (!i)⟩
    (stabilizer_base F i) (stabilizer_base F (!i))
  cases i <;> simpa only [Bool.not_false, Bool.not_true, inf_comm] using h

/-- In a connected graph, fixing every ball is exactly fixing every vertex. -/
theorem iInf_ballKernel (hgen : F false ⊔ F true = ⊤) (v : Vertex F) :
    (⨅ n, ballKernel F v n) = (MulAction.toPermHom G (Vertex F)).ker := by
  ext g
  constructor
  · intro hg
    apply Equiv.Perm.ext
    intro w
    obtain ⟨p⟩ := (connected F hgen) v w
    exact (mem_iInf.mp hg p.length) w p.edist_le
  · intro hg
    apply mem_iInf.mpr
    intro n w _
    exact Equiv.Perm.ext_iff.mp hg w

/-- Thus all centers have the same limiting subgroup: the common normal core. -/
theorem iInf_ballKernel_eq_common_core (hgen : F false ⊔ F true = ⊤) (v : Vertex F) :
    (⨅ n, ballKernel F v n) = (F false ⊓ F true).normalCore := by
  rw [iInf_ballKernel F hgen, global_kernel]

variable [∀ i, Finite (F i)]

/-- Stabilizers remain finite even when the ambient group and graph are infinite. -/
instance finite_stabilizer (v : Vertex F) : Finite (stabilizer F v) := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  have : Finite (stabilizer F (base F v.type)) := by
    simpa only [stabilizer, base, stabilizer_base] using (inferInstance : Finite (F v.type))
  exact Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv

/-- Each finite vertex stabilizer's filtration stabilizes at the common core. -/
theorem ballKernel_stabilizes (hgen : F false ⊔ F true = ⊤) (v : Vertex F) :
    ∃ N : ℕ, ∀ n, N ≤ n → ballKernel F v n = (F false ⊓ F true).normalCore := by
  have : Finite (ballKernel F v 0) := by rw [ballKernel_zero]; infer_instance
  obtain ⟨N, hN⟩ := finite_filtration_stabilizes (ballKernel F v) (ballKernel_antitone F v)
  exact ⟨N, fun n hn => (hN n hn).trans (iInf_ballKernel_eq_common_core F hgen v)⟩

/-- The geometric part of F.7.3(8): one positive radius works at every vertex.
The assembly owner must prove the stated global-kernel hypothesis. -/
theorem uniform_trivial_ballKernel (hgen : F false ⊔ F true = ⊤)
    (hker : (MulAction.toPermHom G (Vertex F)).ker = ⊥) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Vertex F, ∀ n, N ≤ n → ballKernel F v n = ⊥ := by
  have hbase (i : Bool) : ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n → ballKernel F (base F i) n = ⊥ := by
    have : Finite (ballKernel F (base F i) 0) := by rw [ballKernel_zero]; infer_instance
    apply finite_filtration_eventually_bot _ (ballKernel_antitone F _)
    rw [iInf_ballKernel F hgen, hker]
  obtain ⟨N₀, hpos₀, h₀⟩ := hbase false
  obtain ⟨N₁, _, h₁⟩ := hbase true
  refine ⟨max N₀ N₁, hpos₀.trans_le (le_max_left _ _), fun v n hn => ?_⟩
  have hb : ballKernel F (base F v.type) n = ⊥ := by
    cases v.type
    · exact h₀ n ((le_max_left _ _).trans hn)
    · exact h₁ n ((le_max_right _ _).trans hn)
  obtain ⟨g, hg⟩ := exists_smul_base F v
  calc
    ballKernel F v n = ballKernel F (g • base F v.type) n := congrArg (fun w => ballKernel F w n) hg.symm
    _ = (ballKernel F (base F v.type) n).map (MulAut.conj g).toMonoidHom :=
      ballKernel_translate F g _ n
    _ = ⊥ := by rw [hb, map_bot]

theorem uniform_trivial_ballKernel_of_common_core (hgen : F false ⊔ F true = ⊤)
    (hcore : (F false ⊓ F true).normalCore = ⊥) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Vertex F, ∀ n, N ≤ n → ballKernel F v n = ⊥ :=
  uniform_trivial_ballKernel F hgen ((global_kernel F).trans hcore)

end Subgroup.CosetGeometry.RankTwo
