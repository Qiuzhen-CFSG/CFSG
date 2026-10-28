module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedPropagation

/-!
# The terminal-core intersection of the original fixed subgroup

An odd Cartan factor in one full permutation kernel avoids the adjacent
kernel, since their intersection is a two-group. Extend the fixed edge by
one Cartan-fixed neighbor. The local transitivity argument then puts any
commuting Cartan-normalized two-subgroup of the first core in the adjacent
core. For D this supplies D ∩ Q_(alpha') ≤ Q_(alpha'+1).

Source: DGS, *Groups and Graphs* (1985), 9.10(4), printed p.148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A full abelian edge Cartan fixes another neighbor of the second
endpoint, using the original short-path transitivity. -/
theorem edge_cartan_second_fixed_neighbor
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (ht : RootPathTransitive (graph (family P)) G v 2)
    (C : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w) :
    ∃ r : Vertex (family P), (graph (family P)).Adj w r ∧ r ≠ v ∧ C ≤ stabilizer (family P) r := by
  let := finite_endpoints h
  let Γ := family P
  let p : BasedWalk (graph Γ) 1 v := ⟨⟨w,hvw⟩,PUnit.unit⟩
  have hp : p.Nonbacktracking := nonbacktracking_of_geodesic p (SimpleGraph.dist_eq_one_iff_adj.mpr hvw)
  have hCp : C ≤ pathStabilizer Γ p := by
    intro c hc z hz
    change z ∈ [v,w] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl
    · exact (hCE hc).1
    · exact (hCE hc).2
  have hdeg : 1 < ((graph Γ).neighborSet w).ncard := by
    rw [←Nat.card_coe_set_eq,card_neighbors_of_indices Γ
      (fun i => ((Γ (!i)).subgroupOf (Γ i)).index) (fun _ => rfl)]
    exact lt_of_lt_of_le (by decide) (source_valence_ge_three h hS w.type)
  obtain ⟨z,hz,hzne⟩ := Set.exists_ne_of_one_lt_ncard hdeg v
  exact path_cartan_fixed_extension h hB p hp ht hvw
    (by simp [p,BasedWalk.vertices]) (by simp [p,BasedWalk.vertices]) C hCp hd hg inferInstance hz hzne

/-- Kernel exclusion at the next vertex propagates a commuting two-subgroup
from one core to the next. The original edge Cartan supplies its second
fixed neighbor. -/
theorem cartan_centralizer_le_neighbor_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (ht : RootPathTransitive (graph (family P)) G v 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (C A T : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAQ : A ≤ Q (family P) v) (hCA : C ≤ normalizer (A : Set G))
    (hTC : T ≤ C) (hne : T ≠ ⊥)
    (hTA : T ≤ centralizer (A : Set G))
    (hdis : Disjoint T (ballKernel (family P) w 1)) : A ≤ Q (family P) w := by
  obtain ⟨r,hwr,hrv,hCr⟩ := edge_cartan_second_fixed_neighbor h hB hS hvw ht C hCE hd hg
  exact cartan_normalized_centralizing_two_subgroup_le_core h hB hS hvw.symm hwr hrv ew C A T
    (hCE.trans (inf_comm _ _).le) (by simpa only [inf_comm] using hd)
    (by simpa only [inf_comm] using hg)
    (le_inf (hAQ.trans ((source_Z_Q_U h v).2.trans
      ((ballKernel_one_le_edge (family P) hvw).trans inf_le_right)))
      (hAQ.trans (Q_le_stabilizer (family P) v)))
    ((isPGroup_pCoreIn 2 _).to_le hAQ) hCA hTC (hTC.trans hCr) hTA hne hdis

/-- A commuting two-subgroup of one core propagates through an adjacent
kernel when the odd Cartan factor lies in the first full kernel. -/
theorem cartan_kernel_centralizer_le_neighbor_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (ht : RootPathTransitive (graph (family P)) G v 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (C A T : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAQ : A ≤ Q (family P) v) (hCA : C ≤ normalizer (A : Set G))
    (hTC : T ≤ C) (hTk : T ≤ ballKernel (family P) v 1)
    (ho : Odd (Nat.card T)) (hne : T ≠ ⊥)
    (hTA : T ≤ centralizer (A : Set G))
    (hkk : ballKernel (family P) v 1 ⊓ ballKernel (family P) w 1 =
      Q (family P) v ⊓ Q (family P) w) : A ≤ Q (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  obtain ⟨r,hwr,hrv,hCr⟩ := edge_cartan_second_fixed_neighbor h hB hS hvw ht C hCE hd hg
  let R := Q Γ v ⊓ Q Γ w
  let : Finite R := Finite.of_injective (inclusion (inf_le_left.trans (Q_le_stabilizer Γ v)))
    (inclusion_injective _)
  have hpR : IsPGroup 2 R := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hTR : Disjoint T R := by
    obtain ⟨k,hk⟩ := hpR.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hdis : Disjoint T (ballKernel Γ w 1) := by
    apply disjoint_def.mpr
    intro t htT htW
    apply disjoint_def.mp hTR htT
    change t ∈ Q Γ v ⊓ Q Γ w
    rw [←hkk]
    exact ⟨hTk htT,htW⟩
  exact cartan_normalized_centralizing_two_subgroup_le_core h hB hS hvw.symm hwr hrv ew C A T
    (hCE.trans (inf_comm _ _).le) (by simpa only [inf_comm] using hd)
    (by simpa only [inf_comm] using hg)
    (le_inf (hAQ.trans ((source_Z_Q_U h v).2.trans
      ((ballKernel_one_le_edge Γ hvw).trans inf_le_right))) (hAQ.trans (Q_le_stabilizer Γ v)))
    ((isPGroup_pCoreIn 2 _).to_le hAQ) hCA hTC (hTC.trans hCr) hTA hne hdis

/-- The literal terminal intersection of D lies in both neighboring cores.
All full-kernel and Cartan conditions retain the original subgroups. -/
theorem graph_cartan_fixed_terminal_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {l x a' r : Vertex (family P)} (hdr : (graph (family P)).Adj a' r)
    (ht : RootPathTransitive (graph (family P)) G a' 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (er : (graphLocalGroup (family P) r ⧸ pCore 2 (graphLocalGroup (family P) r)) ≃* SL(2,F))
    (C : Subgroup G) [IsMulCommutative C]
    (hCl : C ≤ stabilizer (family P) l)
    (hCE : C ≤ stabilizer (family P) a' ⊓ stabilizer (family P) r)
    (hd : Disjoint C ((stabilizer (family P) a' ⊓ stabilizer (family P) r : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) a' ⊓ stabilizer (family P) r : Subgroup G).pCoreIn 2 =
      stabilizer (family P) a' ⊓ stabilizer (family P) r)
    (hTk : C ⊓ graphLocalGroup (family P) l ≤ ballKernel (family P) a' 1)
    (ho : Odd (Nat.card (C ⊓ graphLocalGroup (family P) l : Subgroup G)))
    (hne : C ⊓ graphLocalGroup (family P) l ≠ ⊥)
    (hkk : ballKernel (family P) a' 1 ⊓ ballKernel (family P) r 1 =
      Q (family P) a' ⊓ Q (family P) r)
    (hDx : Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G) ≤ Q (family P) x) :
    (Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G)) ⊓ Q (family P) a' ≤
      Q (family P) x ⊓ Q (family P) r := by
  let Γ := family P
  let T := C ⊓ graphLocalGroup Γ l
  let D := Q Γ l ⊓ centralizer (T : Set G)
  have hCnT : C ≤ normalizer (T : Set G) :=
    ((le_centralizer C).trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hCnD : C ≤ normalizer (D : Set G) :=
    (le_inf (hCl.trans (stabilizer_normalizes_Q Γ l))
      (hCnT.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hCnA : C ≤ normalizer ((D ⊓ Q Γ a' : Subgroup G) : Set G) :=
    (le_inf hCnD ((hCE.trans inf_le_left).trans (stabilizer_normalizes_Q Γ a'))).trans
      inf_normalizer_le_normalizer_inf
  exact le_inf (inf_le_left.trans hDx)
    (cartan_kernel_centralizer_le_neighbor_core h hB hS hdr ht er C (D ⊓ Q Γ a') T
      hCE hd hg inf_le_right hCnA inf_le_left hTk ho hne
      (le_centralizer_iff.mp (inf_le_left.trans (show D ≤ centralizer (T : Set G) from inf_le_right))) hkk)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
