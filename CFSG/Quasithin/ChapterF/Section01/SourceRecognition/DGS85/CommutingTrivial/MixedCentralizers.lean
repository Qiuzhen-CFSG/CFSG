module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.InitialGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CoreIntersections

/-!
# The mixed centralizers in the small-neighbor case of DGS 9.3

When the opposite neighborhood span lies in Q_beta, it lies in the
starting stabilizer. The starting local center is trivial, so the
centralizer-Sylow alternative identifies its centralizer of Z_alpha
with its intersection with Q_alpha. The forward trivial-displacement
hypothesis gives the reciprocal centralizer in Z_alpha. Critical escape
then forces the opposite span to escape Q_alpha as well.

The final application uses the actual reduced F1.11 graph, discharging
the kernel-Sylow and local-center premises. These are the two centralizer
identities in the second case of 9.3; the natural-section recognition
and terminal distance and field conclusions are not assumed.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
9.3, printed p.142, using 6.2(c,d) and 9.1(b).
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The local centerless case of 6.2(c), for the intrinsic source actor. -/
theorem intrinsic_centerless_centralizer_sylow (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (v : Vertex (family P)) (hz : center (graphLocalGroup (family P) v) = ⊥) :
    ∃ T : Sylow 2 (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G),
      (T : Subgroup (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G)).map
        (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G)).subtype = Q (family P) v := by
  let := finite_endpoints h
  rcases graphLocalGroup_sylow_or_center h hB hS v with hs | he
  · exact hs
  · exfalso
    have hΩ : omegaCenterIn (graphLocalGroup (family P) v) = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      rintro x ⟨y, ⟨z, hz', rfl⟩, rfl⟩
      have hy : (z : graphLocalGroup (family P) v) = 1 := mem_bot.mp (hz ▸ z.property)
      exact mem_bot.mpr (congrArg (graphLocalGroup (family P) v).subtype hy)
    have hbot := he.trans hΩ
    obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
    rw [← hg, Z_translate, map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hbot
    exact base_Z_ne_bot h _ hbot

/-- The forward mixed centralizer is exactly the opposite core intersection. -/
theorem mixed_center_centralizer (h : LocallyRankOneTriple P B)
    (hSyl : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 ≤ b (family P))
    (htriv : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ = ⊥) :
    Z (family P) a ⊓ centralizer (V (family P) a' 1 : Set G) =
      Z (family P) a ⊓ Q (family P) a' := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun v => (source_Z_Q_U h v).1) a
  have hZV : Z (family P) a ≤ V (family P) beta 1 :=
    le_iSup_of_le a (le_iSup_of_le ((mem_ball_one (family P) beta a).mpr (Or.inl hab.symm)) le_rfl)
  apply two_actor_centralizer_eq_core_inter h a' (hSyl a') _
    (IsElementaryAbelian.isPGroup 2 _) (hZV.trans (V_le_stabilizer (family P) h.generate beta a' hd))
  exact bot_unique ((commutator_mono (inf_le_inf_right _ hZV) le_rfl).trans_eq htriv)

/-- In the small-neighbor case the reciprocal mixed centralizer is also exact. -/
theorem mixed_neighbor_centralizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hz : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (hsmall : V (family P) a' 1 ≤ Q (family P) beta) :
    V (family P) a' 1 ⊓ centralizer (Z (family P) a : Set G) =
      V (family P) a' 1 ⊓ Q (family P) a := by
  let := finite_endpoints h
  have hp : IsPGroup 2 (V (family P) a' 1) := (isPGroup_pCoreIn 2 _).to_le hsmall
  have hVa : V (family P) a' 1 ≤ stabilizer (family P) a :=
    hsmall.trans ((source_Z_Q_U h beta).2.trans
      ((ballKernel_one_le_edge (family P) hab.symm).trans inf_le_right))
  exact Noncommuting.inf_centralizer_eq_inf_core _ _ _ _ hp hVa (Q_le_stabilizer _ _)
    (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q (family P) a (source_Z_Q_U h a).1))
    (stabilizer_normalizes_Q (family P) a)
    (intrinsic_centerless_centralizer_sylow h hB hS a
      (intrinsic_local_center_eq_bot_of_neighbor_central h hB hS hab hz))

/-- Critical escape forces the opposite span outside the starting core. -/
theorem mixed_neighbor_escape (h : LocallyRankOneTriple P B)
    (hSyl : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 ≤ b (family P))
    (htriv : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ = ⊥) :
    ¬ V (family P) a' 1 ≤ Q (family P) a := by
  intro hVQ
  have hC : Z (family P) a ≤ centralizer (V (family P) a' 1 : Set G) :=
    (CommutingNontrivial.Z_centralizes_Q (family P) a (source_Z_Q_U h a).1).trans
      (centralizer_le hVQ)
  have he := mixed_center_centralizer h hSyl hab hd htriv
  rw [inf_of_le_left hC] at he
  exact hc.2 (he.le.trans (inf_le_right.trans (source_Z_Q_U h a').2))

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both mixed centralizers and reverse escape on the literal reduced graph. -/
theorem reduced_critical_mixed_centralizers (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥)
    (hsmall : V (Reduction.reducedFamily L S) a' 1 ≤ Q (Reduction.reducedFamily L S) beta) :
    let F := Reduction.reducedFamily L S
    Z F a ⊓ centralizer (V F a' 1 : Set (Reduction.G₀ L S)) = Z F a ⊓ Q F a' ∧
      V F a' 1 ⊓ centralizer (Z F a : Set (Reduction.G₀ L S)) = V F a' 1 ⊓ Q F a ∧
      ¬ V F a' 1 ≤ Q F a := by
  let ht := Reduction.reduced_triple h
  have hz := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  exact ⟨mixed_center_centralizer ht (Reduction.reduced_kernel_sylow h) hab hd.le htriv,
    mixed_neighbor_centralizer ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) hab hz hsmall,
    mixed_neighbor_escape ht (Reduction.reduced_kernel_sylow h) hc hab hd.le htriv⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
