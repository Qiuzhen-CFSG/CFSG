module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ExtendedCartanKernels

/-!
# Propagating the fixed subgroup along the extended path

A two-subgroup normalized by the full Cartan either lies in the vertex
core or is transitive off its fixed neighbor. A commuting nontrivial
Cartan factor fixing a second neighbor would then lie in the whole local
permutation kernel. The original kernel exclusions therefore force core
containment, first at beta and then at alpha-plus-two.

This proves the first propagation in DGS 9.10(4), printed p.148, from the
original radius-two fixed-point bound and the same extended Cartan.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The nontrivial commuting factor and its kernel exclusion force the
Cartan-normalized two-subgroup into the literal vertex core. -/
theorem cartan_normalized_centralizing_two_subgroup_le_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w r : Vertex (family P)}
    (hvw : (graph (family P)).Adj v w) (hvr : (graph (family P)).Adj v r) (hrw : r ≠ w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (C A T : Subgroup G)
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hc : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAE : A ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hp : IsPGroup 2 A) (hn : C ≤ normalizer (A : Set G))
    (hTC : T ≤ C) (hTr : T ≤ stabilizer (family P) r)
    (hTA : T ≤ centralizer (A : Set G))
    (hne : T ≠ ⊥) (hdis : Disjoint T (ballKernel (family P) v 1)) : A ≤ Q (family P) v := by
  by_contra he
  have ht := cartan_normalized_two_subgroup_transitive h hB hS hvw e C A hCE hc hg hAE hp hn he
  have hk := centralizer_le_kernel_of_two_fixed_neighbors hvr hrw A T ht
    (hTC.trans (hCE.trans inf_le_left)) (hTC.trans (hCE.trans inf_le_right)) hTr hTA
  exact hne (le_bot_iff.mp ((le_inf le_rfl hk).trans (disjoint_iff.mp hdis).le))

/-- The original fixed subgroup lies in all three interior path cores.
The terminal vertex is deliberately separate: its core cuts off the
preceding central line in the subsequent direct-product decomposition. -/
theorem graph_cartan_fixed_interior_cores
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {l a beta x a' : Vertex (family P)}
    (hal : (graph (family P)).Adj a l) (hab : (graph (family P)).Adj a beta)
    (hbx : (graph (family P)).Adj beta x) (hxa' : (graph (family P)).Adj x a')
    (hxa : x ≠ a) (hdb : a' ≠ beta)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,K))
    (C : Subgroup G) [IsMulCommutative C]
    (hCl : C ≤ stabilizer (family P) l)
    (hfix : C ≤ stabilizer (family P) a ⊓ stabilizer (family P) beta ⊓
      stabilizer (family P) x ⊓ stabilizer (family P) a')
    (ho : Odd (Nat.card C))
    (hc : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) beta : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) beta : Subgroup G).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) beta)
    (hne : C ⊓ graphLocalGroup (family P) l ≠ ⊥)
    (hb : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) beta 1))
    (hx : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) x 1))
    (hD : Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G) ≤
      ballKernel (family P) l 2) :
    Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G) ≤
      Q (family P) a ⊓ Q (family P) beta ⊓ Q (family P) x := by
  let := finite_endpoints h
  let Γ := family P
  let T := C ⊓ graphLocalGroup Γ l
  let D := Q Γ l ⊓ centralizer (T : Set G)
  have hCE : C ≤ stabilizer Γ a ⊓ stabilizer Γ beta := hfix.trans (inf_le_left.trans inf_le_left)
  have hCb : C ≤ stabilizer Γ beta := hCE.trans inf_le_right
  have hCa : C ≤ stabilizer Γ a := hCE.trans inf_le_left
  have hCx : C ≤ stabilizer Γ x := hfix.trans (inf_le_left.trans inf_le_right)
  have hCd : C ≤ stabilizer Γ a' := hfix.trans inf_le_right
  have hCnT : C ≤ normalizer (T : Set G) :=
    ((le_centralizer C).trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hCnD : C ≤ normalizer (D : Set G) :=
    (le_inf (hCl.trans (stabilizer_normalizes_Q Γ l))
      (hCnT.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 D := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hTa : T ≤ centralizer (D : Set G) := le_centralizer_iff.mp (show D ≤ centralizer (T : Set G) from inf_le_right)
  have hDa : D ≤ Q Γ a := two_subgroup_le_Q Γ a (source_kernel_sylow h hB hS a) hp
    (hD.trans (ballKernel_succ_le Γ hal.symm 1))
  have hcorefix {v w : Vertex Γ} (hvw : (graph Γ).Adj v w) : Q Γ v ≤ stabilizer Γ w :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge Γ hvw).trans inf_le_right)
  have hDb : D ≤ Q Γ beta := by
    apply cartan_normalized_centralizing_two_subgroup_le_core h hB hS hab.symm hbx hxa eb C D T
      (le_inf hCb hCa) (by simpa only [inf_comm] using hc) (by simpa only [inf_comm] using hg)
      (le_inf (hDa.trans (hcorefix hab)) (hDa.trans (Q_le_stabilizer Γ a))) hp hCnD
      inf_le_left (inf_le_left.trans hCx) hTa hne hb
  have hCxb : C ≤ stabilizer Γ x ⊓ stabilizer Γ beta := le_inf hCx hCb
  obtain ⟨hcx,hgx⟩ := path_cartan_complement_at_edge h hab hbx.symm C hCE hCxb ho hc hg
  have hDx : D ≤ Q Γ x := cartan_normalized_centralizing_two_subgroup_le_core h hB hS
    hbx.symm hxa' hdb ex C D T hCxb hcx hgx
    (le_inf (hDb.trans (hcorefix hbx)) (hDb.trans (Q_le_stabilizer Γ beta))) hp hCnD
    inf_le_left (inf_le_left.trans hCd) hTa hne hx
  exact le_inf (le_inf hDa hDb) hDx

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
