module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicCentralNeighbors
public import Theory.GroupTheory.Commutator.NormalModuloSpan

/-!
# Displacement in the beta kernel of the extended Cartan

The preceding local torus centralizes Z_(alpha-1), so its beta-kernel
intersection moves Z_alpha only into Z_beta. Adjoining Q_beta makes this
actor invariant under L_beta, and the same bound propagates to V_beta.
A centralizing element carrying beta to alpha-prime then puts the movement
of Z_(alpha+2) in two disjoint central neighbor lines. The center centralizer
fixes all neighbors, so the established alpha-plus-two exclusion kills it.

The displacement and the reduction from an actual centralizing exchange
are proved here. Construction of that exchange is a separate step.
Source: DGS, *Groups and Graphs* (1985), 9.10(3), printed p.148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem nonbinary_kernel_neighborhood_displacement_of_seed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F)
    (hcore : ⁅Q (family P) beta,V (family P) beta 1⁆ ≤ Z (family P) beta)
    (D : Subgroup G) (hDU : D ≤ ballKernel (family P) beta 1)
    (hseed : ⁅Z (family P) a,D⁆ ≤ Z (family P) beta) :
    ⁅V (family P) beta 1,D⁆ ≤ Z (family P) beta := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ beta
  have hHZ : H ≤ normalizer (Z Γ beta : Set G) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)
  have hDZ : D ≤ normalizer (Z Γ beta : Set G) :=
    (hDU.trans (ballKernel_le_stabilizer Γ beta 1)).trans
      (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)
  have hAH : Z Γ a ≤ H := ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
    (neighbor_core_le_localGroup h hB hS hab.symm)
  have hAQ : ⁅Z Γ a,Q Γ beta⁆ ≤ Z Γ beta := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (CommutingNontrivial.Z_neighbor_le_V Γ hab.symm)).trans hcore
  have hHD : ⁅H,D⁆ ≤ Q Γ beta :=
    (commutator_mono le_rfl hDU).trans
      (nonbinary_actor_kernel_commutator h hB hS hab.symm e hF)
  have hspan := commutator_conjugateSpanBy_le_of_normal_modulo (Z Γ a) H (Q Γ beta) D
    (Z Γ beta) hAH (core_le_graphLocalGroup h beta)
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ beta)) hHZ hDZ hHD hAQ hseed
  rw [CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates Γ H (sylowGenerated_le _) hab.symm
    (fun z hz => graphLocalGroup_transitive h hB hS beta ⟨a,hab.symm⟩ ⟨z,hz⟩)]
  exact commutator_sup_le_of_relative_normal H _ _ _ _ hHZ
    (((source_Z_Q_U h beta).1.trans (map_subtype_le _)).trans (core_le_graphLocalGroup h beta))
    (conjugateSpanBy_le_self hAH)
    (le_normalizer_iff_commutator_le_left.mp hDZ) hspan


/-- The preceding torus supplies the seed bound in the original beta kernel. -/
theorem extended_cartan_beta_kernel_displacement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta l : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hal : (graph (family P)).Adj a l)
    (hω : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (hspan : Z (family P) a = Z (family P) beta ⊔ Z (family P) l)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F)
    (hcore : ⁅Q (family P) beta,V (family P) beta 1⁆ ≤ Z (family P) beta)
    (T : Subgroup G) (hTL : T ≤ graphLocalGroup (family P) l) :
    ⁅V (family P) beta 1,T ⊓ ballKernel (family P) beta 1⁆ ≤ Z (family P) beta := by
  let := finite_endpoints h
  let Γ := family P
  let D := T ⊓ ballKernel Γ beta 1
  obtain ⟨g,_,hgl⟩ := locally_transitive Γ hab hal
  have hωl : Z Γ l = omegaCenterIn (graphLocalGroup Γ l) := by
    rw [←hgl,Z_translate,graphLocalGroup_conjugate h,
      ←NilesRankOneKernel.omegaCenterIn_map_injective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hω]
  have hlD : Z Γ l ≤ centralizer (D : Set G) := by
    intro z hz
    exact centralizer_le (inf_le_left.trans hTL)
      ((mem_omegaCenterIn_iff _ _).mp (hωl ▸ hz)).2.1
  have hZaSt : Z Γ a ≤ stabilizer Γ beta :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge Γ hab).trans inf_le_right))
  have hseed : ⁅Z Γ a,D⁆ ≤ Z Γ beta := by
    conv_lhs => rw [hspan]
    apply commutator_sup_le_of_relative_normal (Z Γ a) _ _ _ _
      (hZaSt.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ beta))
      (hspan ▸ le_sup_left) (hspan ▸ le_sup_right)
    · exact le_normalizer_iff_commutator_le_left.mp
        ((show D ≤ ballKernel Γ beta 1 from inf_le_right).trans
          ((ballKernel_le_stabilizer Γ beta 1).trans
            (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)))
    · exact (commutator_eq_bot_iff_le_centralizer.mpr hlD).le.trans bot_le
  exact nonbinary_kernel_neighborhood_displacement_of_seed h hB hS hab e hF hcore D
    inf_le_right hseed

/-- A center containing its neighbor center detects the full local action. -/
theorem center_centralizer_le_kernel_of_neighbor_center
    (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hZv : Z (family P) w ≤ Z (family P) v) :
    stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) ≤
      ballKernel (family P) v 1 := by
  let := finite_endpoints h
  let Γ := family P
  let C := stabilizer Γ v ⊓ centralizer (Z Γ v : Set G)
  have hn : stabilizer Γ v ≤ normalizer (C : Set G) :=
    (le_inf (stabilizer Γ v).le_normalizer
      ((CommutingNontrivial.stabilizer_normalizes_Z Γ v).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  by_contra he
  have hcover := CommutingNontrivial.source_normal_sup_edge h hvw C inf_le_left hn he
  have hCw : C ≤ normalizer (Z Γ w : Set G) :=
    (inf_le_right.trans (centralizer_le hZv)).trans (Subgroup.centralizer_le_normalizer _)
  have hNv : stabilizer Γ v ≤ normalizer (Z Γ w : Set G) := by
    rw [←hcover]
    exact sup_le hCw (inf_le_right.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ w))
  have hbot : Z Γ w = ⊥ := by
    apply CommutingNontrivial.source_normalized_edge_eq_bot h hvw _
      (le_inf (hZv.trans (Z_le_stabilizer Γ v)) (Z_le_stabilizer Γ w))
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := locally_transitive Γ hvw hz
      exact ⟨g,hNv hg,hgz⟩
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := locally_transitive Γ hvw.symm hz
      exact ⟨g,CommutingNontrivial.stabilizer_normalizes_Z Γ w hg,hgz⟩
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base Γ w
  rw [←hg,Z_translate,map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hbot
  exact base_Z_ne_bot h _ hbot

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The centralizing exchange closes the beta exclusion on the literal path. -/
theorem reduced_beta_kernel_eq_bot_of_centralizing_exchange
    (h : HypothesisF11 L S)
    {beta x a' : Vertex (Reduction.reducedFamily L S)}
    (hbx : (graph (Reduction.reducedFamily L S)).Adj beta x)
    (hxa' : (graph (Reduction.reducedFamily L S)).Adj x a') (hne : beta ≠ a')
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    (D : Subgroup (Reduction.G₀ L S))
    (hDx : D ≤ stabilizer (Reduction.reducedFamily L S) x)
    (hdisp : ⁅V (Reduction.reducedFamily L S) beta 1,D⁆ ≤ Z (Reduction.reducedFamily L S) beta)
    (hdis : Disjoint D (ballKernel (Reduction.reducedFamily L S) x 1))
    (g : Reduction.G₀ L S) (hgD : g ∈ centralizer (D : Set (Reduction.G₀ L S)))
    (hgb : g • beta = a') : D = ⊥ := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hgm : D.map (MulAut.conj g).toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hgD)
  have hdisp' := map_mono (f := (MulAut.conj g).toMonoidHom) hdisp
  rw [map_commutator,←V_translate,←Z_translate,hgb,hgm] at hdisp'
  have hcom : ⁅Z Γ x,D⁆ = ⊥ := by
    apply bot_unique
    have hle : ⁅Z Γ x,D⁆ ≤ Z Γ beta ⊓ Z Γ a' := le_inf
      ((commutator_mono (CommutingNontrivial.Z_neighbor_le_V Γ hbx) le_rfl).trans hdisp)
      ((commutator_mono (CommutingNontrivial.Z_neighbor_le_V Γ hxa'.symm) le_rfl).trans hdisp')
    exact hle.trans_eq (disjoint_iff.mp
      (Reduction.reduced_intrinsic_central_neighbor_centers_disjoint h hbx.symm hxa' hne hω))
  have hDker : D ≤ ballKernel Γ x 1 :=
    (le_inf hDx (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcom))).trans
      (center_centralizer_le_kernel_of_neighbor_center ht hbx.symm
        (hω ▸ intrinsic_local_omega_le_neighbor_Z ht
          (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hbx))
  exact disjoint_self.mp (hdis.mono_right hDker)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
