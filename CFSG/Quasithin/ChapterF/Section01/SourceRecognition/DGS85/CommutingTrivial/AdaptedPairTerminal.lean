module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedPairFixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedTerminal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborKernels

/-!
# The terminal graph contradiction for the adapted subgroup

If the odd middle actor were in the remote full permutation kernel, coprime
movement and the local actor–kernel commutator bound would put M ∩ Q_d in
Q_r, contradicting the adapted-factor escape. Its fixed subgroup therefore
propagates to Q_r by Cartan transitivity. Equal orders then identify the
normal neighboring intersection with V_d, which the two local graph actions
force to be trivial.

Source: DGS, *Groups and Graphs* (1985), printed p.150, final paragraph of 9.10,
and the normalized-edge obstruction 3.2(c).
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
private theorem terminal_coprime_decomposition (N T : Subgroup G) [Finite N] [Finite T]
    (hn : T ≤ normalizer (N : Set G)) (hs : Group.IsSolvable N)
    (hc : Nat.Coprime (Nat.card T) (Nat.card N)) :
    N = ⁅N,T⁆ ⊔ (N ⊓ centralizer (T : Set G)) := by
  let : Normalizes T N := ⟨hn⟩
  have he := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := N) (A := T) hs hc
  have hm := congrArg (fun U : Subgroup N => U.map N.subtype) he
  rw [Subgroup.map_sup,commutatorAction_subgroup_conj_map_eq_commutator N T hn,
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn N T hn,
    map_subgroupOf_eq_of_le (show subgroupCentralizerIn N T ≤ N from inf_le_left),
    ←MonoidHom.range_eq_map,range_subtype,sup_comm] at hm
  exact hm.symm



/-- An odd actor fixing no point of M cannot lie in the remote full kernel
when the actual subgroup M ∩ Q_d escapes Q_r. -/
theorem adapted_actor_not_le_remote_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {x d r : Vertex (family P)} (hdr : (graph (family P)).Adj d r)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (er : (graphLocalGroup (family P) r ⧸ pCore 2 (graphLocalGroup (family P) r)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F)
    (M T : Subgroup G) (hMQ : M ≤ Q (family P) x)
    (hnM : T ≤ normalizer (M : Set G))
    (hTd : T ≤ stabilizer (family P) d) (ho : Odd (Nat.card T))
    (hfix : M ⊓ centralizer (T : Set G) = ⊥)
    (hesc : ¬ M ⊓ Q (family P) d ≤ Q (family P) r) :
    ¬ T ≤ ballKernel (family P) r 1 := by
  let := finite_endpoints h
  let Γ := family P
  let A := M ⊓ Q Γ d
  let : Finite A := Finite.of_injective (inclusion (inf_le_right.trans (Q_le_stabilizer Γ d)))
    (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion hTd) (inclusion_injective _)
  intro hTk
  have hp : IsPGroup 2 A := (isPGroup_pCoreIn 2 _).to_le (inf_le_left.trans hMQ)
  have hcop : Nat.Coprime (Nat.card T) (Nat.card A) := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hnorm : T ≤ normalizer (A : Set G) :=
    (le_inf hnM (hTd.trans (stabilizer_normalizes_Q Γ d))).trans inf_normalizer_le_normalizer_inf
  have hdec := terminal_coprime_decomposition A T hnorm
    (@IsNilpotent.to_isSolvable A _ hp.isNilpotent) hcop
  have hc : A ⊓ centralizer (T : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (show A ≤ M from inf_le_left)).trans hfix.le)
  rw [hc,sup_bot_eq] at hdec
  apply hesc
  change A ≤ Q Γ r
  rw [hdec]
  exact (commutator_mono (inf_le_right.trans (neighbor_core_le_localGroup h hB hS hdr.symm)) hTk).trans
    (nonbinary_actor_kernel_commutator h hB hS hdr.symm er hF)

/-- The original Cartan transports the odd fixed subgroup into Q_r once
its factor escapes the full r-kernel. -/
theorem adapted_fixed_le_remote_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {d r : Vertex (family P)} (hdr : (graph (family P)).Adj d r)
    (ht : RootPathTransitive (graph (family P)) G d 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (er : (graphLocalGroup (family P) r ⧸ pCore 2 (graphLocalGroup (family P) r)) ≃* SL(2,F))
    (C R T : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) d ⊓ stabilizer (family P) r)
    (hdis : Disjoint C ((stabilizer (family P) d ⊓ stabilizer (family P) r : Subgroup G).pCoreIn 2))
    (hsup : C ⊔ (stabilizer (family P) d ⊓ stabilizer (family P) r : Subgroup G).pCoreIn 2 =
      stabilizer (family P) d ⊓ stabilizer (family P) r)
    (hRd : R ≤ Q (family P) d) (hnR : C ≤ normalizer (R : Set G))
    (hTC : T ≤ C) (hTR : T ≤ centralizer (R : Set G))
    (hesc : ¬ T ≤ ballKernel (family P) r 1) : R ≤ Q (family P) r := by
  let := finite_endpoints h
  let Γ := family P
  obtain ⟨s,hrs,hsd,hCs⟩ := edge_cartan_second_fixed_neighbor h hB hS hdr ht C hCE hdis hsup
  by_contra hRr
  have htrans := cartan_normalized_two_subgroup_transitive h hB hS hdr.symm er C R
    (hCE.trans (inf_comm _ _).le) (by simpa only [inf_comm] using hdis)
    (by simpa only [inf_comm] using hsup)
    (le_inf (hRd.trans ((source_Z_Q_U h d).2.trans
      ((ballKernel_one_le_edge Γ hdr).trans inf_le_right))) (hRd.trans (Q_le_stabilizer Γ d)))
    ((isPGroup_pCoreIn 2 _).to_le hRd) hnR hRr
  exact hesc (centralizer_le_kernel_of_two_fixed_neighbors hrs hsd R T htrans
    (hTC.trans (hCE.trans inf_le_right)) (hTC.trans (hCE.trans inf_le_left)) (hTC.trans hCs) hTR)

/-- The original neighboring core intersection cannot equal the nontrivial
neighbor span while remaining normal in the middle local actor. -/
theorem adapted_intersection_span_contradiction
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {x d : Vertex (family P)} (hd : (graph (family P)).Adj x d)
    (hb : 1 ≤ b (family P))
    (N : Subgroup G) (hNV : N ≤ V (family P) d 1)
    (hNx : graphLocalGroup (family P) x ≤ normalizer (N : Set G))
    (hVQ : V (family P) d 1 ≤ Q (family P) x)
    (q : ℕ) (hq : 1 < q)
    (hNcard : Nat.card N = q^3) (hVcard : Nat.card (V (family P) d 1) = q^3) : False := by
  let := finite_endpoints h
  let Γ := family P
  let : Finite (V Γ d 1) := Finite.of_injective (inclusion (hVQ.trans (Q_le_stabilizer Γ x)))
    (inclusion_injective _)
  have he : N = V Γ d 1 := eq_of_le_of_card_ge hNV (by rw [hNcard,hVcard])
  have hNx' : graphLocalGroup Γ x ≤ normalizer (V Γ d 1 : Set G) := he ▸ hNx
  have hVbot : V Γ d 1 = ⊥ := by
    apply CommutingNontrivial.source_normalized_edge_eq_bot h hd (V Γ d 1)
      (le_inf (hVQ.trans (Q_le_stabilizer Γ x)) (V_le_stabilizer Γ h.generate d d (by simpa only [SimpleGraph.dist_self,zero_add] using hb)))
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive h hB hS x ⟨d,hd⟩ ⟨z,hz⟩
      exact ⟨g,hNx' hg,hgz⟩
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive h hB hS d ⟨x,hd.symm⟩ ⟨z,hz⟩
      exact ⟨g,stabilizer_normalizes_V Γ d 1 (sylowGenerated_le _ hg),hgz⟩
  rw [hVbot,card_bot] at hVcard
  have hpow : 1 < q^3 := one_lt_pow₀ hq (by decide : 3 ≠ 0)
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
