module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic

/-!
# Fixed preimages and transport in the terminal selection

Containment in B is containment in V together with a commutator bound in Z
for the actual two-residual. This characterization transports escaping
radius-two displacements between M-type vertices of the free-amalgam graph.
It retains B as the fixed preimage on V/Z, distinct from the fixed core D.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation p.881 and the all-rho argument in (4.4.1), p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  {geometry : Geometry R}

open scoped commutatorElement in
/-- The fixed-preimage condition uses the actual residual action on V/Z. -/
theorem le_B_iff (hb : 2 < geometry.b R) {c : Vertex R} (hc : color R c = false)
    (A : Subgroup (FreeAmalgam R)) :
    A ≤ B R c (geometry.Z_normal c) ↔ A ≤ V R c ∧ ⁅A, Ltilde R c⁆ ≤ Z R c := by
  have hV : V R c ≤ stabilizer R c := (geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1)
  constructor
  · intro h
    refine ⟨fun x hx => ((mem_B_iff R c _ hV x).mp (h hx)).1, ?_⟩
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R c _ hV x).mp (h hx)).2 l hl
  · rintro ⟨hAV, hcomm⟩ x hx
    apply (mem_B_iff R c _ hV x).mpr
    refine ⟨hAV hx, fun l hl => ?_⟩
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator hl hx)

/-- Conjugation transports B-containment with its center and actual subgroup. -/
theorem map_le_B_act_iff (hb : 2 < geometry.b R) {c : Vertex R}
    (hc : color R c = false) (g : FreeAmalgam R) (A : Subgroup (FreeAmalgam R)) :
    A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      B R (act R g c) (geometry.Z_normal _) ↔ A ≤ B R c (geometry.Z_normal c) := by
  rw [le_B_iff hb (by rwa [action_preserves_color]), le_B_iff hb hc,
    V_act, Ltilde_act, Z_act, ← map_commutator]
  exact and_congr (Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective)
    (Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective)

/-- One escaping rho yields an escaping neighbor at every M-type center. -/
theorem escape_at_any_center (hb : 2 < geometry.b R) {c v : Vertex R}
    (hc : color R c = false) (hv : color R v = false)
    (he : ∃ rho, (cosetGraph R).dist c rho = 2 ∧
      ¬ ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ∃ lam, (cosetGraph R).dist v lam = 2 ∧
      ¬ ⁅Z R lam, Q R v⁆ ≤ B R v (geometry.Z_normal v) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R hc
  obtain ⟨h, rfl⟩ := exists_mVertex_of_color R hv
  obtain ⟨rho, hd, hn⟩ := he
  let k := g⁻¹ * h
  have hk : act R k (mVertex R g) = mVertex R h := by simp [k, act_mVertex]
  refine ⟨act R k rho, ?_, ?_⟩
  · rw [← hk, dist_act]
    exact hd
  · intro hf
    apply hn
    have hf' : (⁅Z R rho, Q R (mVertex R g)⁆).map
        (MulAut.conj k⁻¹).toMonoidHom ≤ B R (act R k (mVertex R g)) (geometry.Z_normal _) := by
      rwa [map_commutator, ← Z_act, ← Q_act, hk]
    exact (map_le_B_act_iff hb rfl k _).mp hf'

/-- The universal fixedness assumption transports without adding a universal
nonnaturality assumption. -/
theorem all_fixed_at_any_center (hb : 2 < geometry.b R) {c : Vertex R}
    (hc : color R c = false)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    {v : Vertex R} (hv : color R v = false) :
    ∀ rho, (cosetGraph R).dist v rho = 2 →
      ⁅Z R rho, Q R v⁆ ≤ B R v (geometry.Z_normal v) := by
  intro rho hd
  by_contra hn
  obtain ⟨rho', hd', hn'⟩ := escape_at_any_center hb hv hc ⟨rho, hd, hn⟩
  exact hn' (hall rho' hd')

/-- The all-rho assumption controls the full radius displacement, including
its distance-zero and distance-one generators. -/
theorem radius_displacement_le_B (hb : 2 < geometry.b R) {c : Vertex R}
    (hc : color R c = false)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ⁅V R c, Q R c⁆ ≤ B R c (geometry.Z_normal c) := by
  have hVQ := geometry.V_le_Q hb c hc
  change ⁅⨆ rho, ⨆ (_ : (cosetGraph R).dist rho c ≤ 2), Z R rho, Q R c⁆ ≤ _
  rw [commutator_iSup_of_le _ _ (fun rho => (le_iSup _ rho).trans hVQ)]
  apply iSup_le
  intro rho
  rw [commutator_iSup_of_le _ _ (fun hd =>
    (le_iSup_of_le rho (le_iSup_of_le hd le_rfl)).trans hVQ)]
  apply iSup_le
  intro hd
  by_cases htwo : (cosetGraph R).dist rho c = 2
  · exact hall rho (by rwa [SimpleGraph.dist_comm])
  have hle : Z R rho ≤ Z R c := by
    have hcases : (cosetGraph R).dist rho c = 0 ∨ (cosetGraph R).dist rho c = 1 := by omega
    rcases hcases with hzero | hone
    · have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
      subst rho
      exact le_rfl
    · exact Escape.EdgeTransfer.edge_Z_le c rho hc
        (adjacent_symm R ((cosetGraph_adj R _ _).mp
          (SimpleGraph.dist_eq_one_iff_adj.mp hone)))
  exact (commutator_mono hle le_rfl).trans
    ((geometry.centralizes c hc).le.trans bot_le)

/-- The literal triple-commutator premise for the quotient module at any
M-type center follows from the single original all-rho assumption. -/
theorem radius_triple_le_Z_at_any_center (hb : 2 < geometry.b R) {c : Vertex R}
    (hc : color R c = false)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    {v : Vertex R} (hv : color R v = false) :
    ⁅⁅V R v, Q R v⁆, Ltilde R v⁆ ≤ Z R v :=
  ((le_B_iff hb hv _).mp
    (radius_displacement_le_B hb hv (all_fixed_at_any_center hb hc hall hv))).2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
