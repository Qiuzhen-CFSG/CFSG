module
public import Theory.GroupTheory.Hall.TwoComplementConjugacy
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.PathCartanExtension
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceLinearPaths

/-!
# A full Cartan and both transporters on the critical four-path

The intrinsic noncommuting catalogue and the first nonregular path theorem
give s ≥ 4. Thus a full odd abelian edge complement fixes any prescribed
nonbacktracking four-path. It is the product of its two intrinsic local tori.

The intrinsic actor moves between neighbors. The two full complements in the
destination edge are conjugate by its two-core, which lies in that same
actor and fixes the destination. This corrects the transporter into the
normalizer of the whole Cartan, including its factor outside the actor.
The literal path (t, alpha, beta, alpha', y) consequently supplies both
transporters used in the residual argument without a quotient marking premise.

Source: DGS, Groups and Graphs (1985), 6.8, p.124, and the opening Cartan
choices in (10.8), p.160. Residual separation remains a subsequent argument.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "s₀" => DGS85.sourceS (P := fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- The actual first nonregular path has length at least four in the noncommuting branch. -/
theorem noncommuting_source_length_ge_four
    (h : HypothesisF11 L S) {v w : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) : 4 ≤ s₀ := by
  obtain ⟨n, hs, i, p, hp, hn, _, _⟩ := reduced_sourceS_path_complement h
  obtain ⟨m, hm, K, fK, finK, hK, ⟨eK⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne p.endpoint
  let _ := fK
  let _ := finK
  let _ : Fintype K := Fintype.ofFinite K
  let _ : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  exact (reduced_sourceS_linear_path h hs p hp eK hn).2

/-- Construct the full abelian edge complement fixing a prescribed four-path. -/
theorem noncommuting_four_path_cartan
    (h : HypothesisF11 L S) {v w z a b : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (p : BasedWalk (graph F) 4 z) (hp : p.Nonbacktracking)
    (hab : (graph F).Adj a b) (ha : a ∈ p.vertices) (hb : b ∈ p.vertices) :
    let E := stabilizer F a ⊓ stabilizer F b
    ∃ C : Subgroup (G₀ L S),
      C ≤ pathStabilizer F p ∧ Disjoint C (E.pCoreIn 2) ∧
      C ⊔ E.pCoreIn 2 = E ∧ Odd (Nat.card C) ∧ IsMulCommutative C ∧
      C = (C ⊓ graphLocalGroup F a) ⊔ (C ⊓ graphLocalGroup F b) := by
  obtain ⟨m, hm, K, fK, finK, hK, ⟨eK⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne a
  obtain ⟨n, hn, J, fJ, finJ, hJ, ⟨eJ⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne b
  let _ := fK
  let _ := finK
  let _ := fJ
  let _ := finJ
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype J := Fintype.ofFinite J
  let _ : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let _ : CharP J 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hJ)
  let eK' := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  let eJ' := eJ.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi J)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have ht := sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) z
    (noncommuting_source_length_ge_four h hc hne)
  obtain ⟨C, hCp, hdis, hsup, ho, hcomm, _, _, hprod⟩ :=
    CommutingTrivial.reduced_linear_path_cartan h p hp ht hab ha hb eK' eJ'
  exact ⟨C, hCp, hdis, hsup, ho, hcomm, hprod⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
/-- Transport between Cartan-fixed neighbors inside the intrinsic actor and full Cartan normalizer. -/
theorem full_cartan_neighbor_transport
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w t : Vertex (family P)}
    (hvw : (graph (family P)).Adj v w) (hvt : (graph (family P)).Adj v t)
    (K : Subgroup G) [IsMulCommutative K]
    (hKE : K ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hKt : K ≤ stabilizer (family P) t)
    (ho : Odd (Nat.card K))
    (hd : Disjoint K ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hgen : K ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w) :
    ∃ g ∈ graphLocalGroup (family P) v,
      g ∈ normalizer (K : Set G) ∧ g • w = t := by
  let _ := finite_endpoints h
  let Γ := family P
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let D := stabilizer Γ v ⊓ stabilizer Γ t
  let Q := D.pCoreIn 2
  have hKD : K ≤ D := le_inf (hKE.trans inf_le_left) hKt
  let _ : Finite K := Finite.of_injective (inclusion (hKE.trans inf_le_left))
    (inclusion_injective _)
  let _ : Finite Q := Finite.of_injective
    (inclusion ((pCoreIn_le 2 D).trans inf_le_left)) (inclusion_injective _)
  let _ : Group.IsSolvable K := Group.isSolvable_of_comm (mul_comm' (M := K))
  obtain ⟨a,ha,hat⟩ := locally_transitive Γ hvw hvt
  obtain ⟨g,hg,b,hb,hgb⟩ := graph_intrinsic_edge_factor h hB hS hvw a ha
  have hgw : g • w = t := by
    simpa only [hgb,mul_smul,show b • w = w from hb.2] using hat
  have hgv : g • v = v := sylowGenerated_le _ hg
  let C := K.map (MulAut.conj g).toMonoidHom
  let _ : Finite C := Finite.of_equiv K (K.equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv
  have hmapE : E.map (MulAut.conj g).toMonoidHom = D := by
    dsimp only [E,D]
    rw [map_inf _ _ _ (MulAut.conj g).injective,←stabilizer_translate,
      ←stabilizer_translate,hgv,hgw]
  have hCD : C ≤ D := hmapE ▸ map_mono hKE
  have hnorm : D ≤ normalizer (Q : Set G) := D.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  have hCQ : C ⊔ Q = D := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (MulAut.conj g).injective,hmapE] at hh
    exact hh
  have hKQ : K ⊔ Q = D := (CommutingTrivial.path_cartan_complement_at_edge h
    hvw hvt K hKE hKD ho hd hgen).2
  have hCo : Nat.Coprime 2 (Nat.card C) := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact Nat.coprime_two_left.mpr ho
  obtain ⟨q,hq,hqC⟩ := OddHall.exists_two_conjugator_of_common_sup Q K C
    (isPGroup_pCoreIn 2 D) (Nat.coprime_two_left.mpr ho) hCo
    (hKD.trans hnorm) (hCD.trans hnorm)
    (by rw [sup_comm Q C,hCQ,sup_comm Q K,hKQ])
  refine ⟨q*g,(graphLocalGroup Γ v).mul_mem (graph_intrinsic_edgeCore_le h hq) hg,?_,?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change K.map (MulAut.conj (q*g)).toMonoidHom = K
    change (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj q).toMonoidHom = K at hqC
    rw [Subgroup.map_map] at hqC
    convert hqC using 2
    ext z
    simp [mul_assoc]
  · rw [mul_smul,hgw]
    exact ((pCoreIn_le 2 D) hq).2
end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- One full Cartan fixes the actual critical four-path and supplies both source transporters. -/
theorem original_bTwo_path_cartan_transport
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β) :
    let E := stabilizer F α ⊓ stabilizer F β
    ∃ K : Subgroup (G₀ L S),
      K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
        stabilizer F u ⊓ stabilizer F y ∧
      Disjoint K (E.pCoreIn 2) ∧ K ⊔ E.pCoreIn 2 = E ∧
      Odd (Nat.card K) ∧ IsMulCommutative K ∧
      K = (K ⊓ graphLocalGroup F α) ⊔ (K ⊓ graphLocalGroup F β) ∧
      (∃ g ∈ graphLocalGroup F α, g ∈ normalizer (K : Set (G₀ L S)) ∧ g • β = t) ∧
      (∃ a ∈ graphLocalGroup F β, a ∈ normalizer (K : Set (G₀ L S)) ∧ a • α = u) := by
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hua : u ≠ α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    omega
  let p : BasedWalk (graph F) 4 t :=
    ⟨⟨α,ht.symm⟩,⟨⟨β,hab⟩,⟨⟨u,hβu⟩,⟨⟨y,hy⟩,PUnit.unit⟩⟩⟩⟩
  have hp : p.Nonbacktracking := ⟨Ne.symm htne,hua,hyne,True.intro⟩
  have hpa : α ∈ p.vertices := by change α ∈ [t,α,β,u,y]; simp
  have hpb : β ∈ p.vertices := by change β ∈ [t,α,β,u,y]; simp
  obtain ⟨K,hKp,hd,hgen,ho,hcomm,hprod⟩ :=
    noncommuting_four_path_cartan h hc hne p hp hab hpa hpb
  have hfix : K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
      stabilizer F u ⊓ stabilizer F y := by
    intro k hk
    have hh := hKp hk
    exact ⟨⟨⟨⟨hh t (by change t ∈ [t,α,β,u,y]; simp),hh α hpa⟩,
      hh β hpb⟩,hh u (by change u ∈ [t,α,β,u,y]; simp)⟩,
      hh y (by change y ∈ [t,α,β,u,y]; simp)⟩
  have hKE : K ≤ stabilizer F α ⊓ stabilizer F β :=
    le_inf (fun k hk => (hfix hk).1.1.1.2) (fun k hk => (hfix hk).1.1.2)
  let _ := hcomm
  refine ⟨K,hfix,hd,hgen,ho,hcomm,hprod,?_,?_⟩
  · exact full_cartan_neighbor_transport (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab ht K hKE
      (fun k hk => (hfix hk).1.1.1.1) ho hd hgen
  · apply full_cartan_neighbor_transport (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hab.symm hβu K
      (hKE.trans (inf_comm _ _).le) (fun k hk => (hfix hk).1.2) ho
    · change Disjoint K ((stabilizer F β ⊓ stabilizer F α).pCoreIn 2)
      simpa only [inf_comm (stabilizer F β) (stabilizer F α)] using hd
    · change K ⊔ (stabilizer F β ⊓ stabilizer F α).pCoreIn 2 =
        stabilizer F β ⊓ stabilizer F α
      simpa only [inf_comm (stabilizer F β) (stabilizer F α)] using hgen
end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
