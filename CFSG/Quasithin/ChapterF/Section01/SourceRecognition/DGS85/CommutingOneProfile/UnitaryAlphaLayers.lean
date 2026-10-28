module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryMarkedCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaCenterMinimal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaSecondKernel

/-!
# Alpha center irreducibility and neighboring-core vanishing

The marked field relation and center order put Z_alpha at the minimum
faithful binary degree, so the alpha local group acts irreducibly on it.
The beta core is special with center Z_beta. Its normal subgroup formed
by the intersection of all neighboring beta cores is disjoint from that
center along the constructed escaping turn, hence trivial.

UnitaryAlphaFrattini uses these two alternatives to force Z_alpha into
Phi(Q_alpha), without a path-transitivity input.
Source: DGS85, Groups and Graphs, (5.7), (11.6), (11.8), pp.108,172--176.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
private theorem center_minimal_of_degree
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (n : ℕ) (hn : 0 < n) (hk : Nat.card k = 2^n)
    (hsize : Nat.card (Z (family P) a) = 2^(2*n))
    (Y : Subgroup G) (hY : Y ≤ Z (family P) a)
    (hN : d.localGroup a ≤ normalizer (Y : Set G)) :
    Y = ⊥ ∨ Y = Z (family P) a := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let V := Z (family P) a
  let : Finite V := Finite.of_injective (inclusion (Z_le_stabilizer _ a)) (inclusion_injective _)
  have hV : V ≠ ⊥ := by
    intro he
    apply hc.2
    change V ≤ U (family P) b
    rw [he]
    exact bot_le
  let : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV
  have hz := local_center_eq_bot_of_neighbor_central h d (source_critical_one_adjacent hc hb)
    (critical_end_center_of_commuting (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
      (d.localGroup b) (d.sylow_or_center b))
  obtain ⟨ρ,hact⟩ := source_exists_center_quotient_action h d a ea
  obtain ⟨S,_,_,hres⟩ := source_center_module_prepared_of_center_eq_bot h d a hz default ea ρ hact
  have hfix : ρ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    exact hres.le (fun g => hv g.val)
  have hdim : Module.finrank (ZMod 2) (Additive V) = 2*n := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hh
    rw [hsize,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh).symm
  let := Representation.SL2.irreducible_of_fixed_free_minimal_binary_degree
    ρ hfix (by omega) hk hdim.le
  let W : Subrepresentation ρ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (Y.subgroupOf V).toAddSubgroup
    apply_mem_toSubmodule := by
      intro t z hz
      obtain ⟨l,hl⟩ := (ea.surjective.comp (QuotientGroup.mk'_surjective _)) t
      change ((ρ t z).toMul : G) ∈ Y
      rw [←hl]
      change ((ρ (ea (QuotientGroup.mk' (pCore 2 (d.localGroup a)) l)) z).toMul : G) ∈ Y
      rw [hact]
      exact (mem_normalizer_iff.mp (hN l.property) (z.toMul : G)).mp hz }
  rcases eq_bot_or_eq_top W with he | he
  · left
    apply bot_unique
    intro y hy
    have hm : Additive.ofMul (⟨y,hY hy⟩ : V) ∈ W.toSubmodule := hy
    rw [he] at hm
    exact congrArg (fun v : Additive V => (v.toMul : G)) hm
  · right
    apply le_antisymm hY
    intro z hz
    have hm : Additive.ofMul (⟨z,hz⟩ : V) ∈ W.toSubmodule := by rw [he]; trivial
    exact hm

theorem source_unitary_alpha_center_minimal
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m)) :
    ∀ Y : Subgroup G, Y ≤ Z (family P) a →
      d.localGroup a ≤ normalizer (Y : Set G) → Y = ⊥ ∨ Y = Z (family P) a := by
  obtain ⟨hfield,n,hn,hi,hq⟩ := source_unitary_field_parameters_from_marking h hB hS d hc hb hcomm hbc hac Ma hm mark
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have ho := (source_unitary_center_seed_pair_orders h hB hS d hc hb hcomm hbc hac Ma hm mark).2.2.1
  have hsize : Nat.card (Z (family P) a) = 2^(2*n) := by
    rw [←hfield,←hq,←pow_two,←pow_mul] at ho
    simpa only [Nat.mul_comm n 2] using ho
  exact center_minimal_of_degree h d hc hb hcomm (ea.trans ep.symm) n (by omega) hk hsize
private theorem normal_subgroup_of_special_disjoint_center
    (N R C : Subgroup G) (hNR : N ≤ R)
    (hn : R ≤ normalizer (N : Set G))
    (hder : ⁅R,R⁆ ≤ C) (hcent : centerIn R = C)
    (hd : N ⊓ C = ⊥) : N = ⊥ := by
  have hcomm : ⁅N,R⁆ = ⊥ := by
    apply bot_unique
    apply le_trans ?_ hd.le
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hn)
      ((commutator_mono hNR le_rfl).trans hder)
  have hNC : N ≤ C := hcent ▸ le_inf hNR
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact bot_unique ((le_inf le_rfl hNC).trans hd.le)

/-- The intersection over all neighboring beta cores is trivial at alpha. -/
theorem source_unitary_alpha_neighbor_core_eq_bot
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m)) :
    neighborCoreIntersection (family P) a = ⊥ := by
  obtain ⟨c₁,hbc₁,hac₁,g,hga,hgb,hesc,_⟩ :=
    source_unitary_beta_escaping_four_walk h hB hS d hc hb hcomm Ma hm mark

  have hab := source_critical_one_adjacent hc hb
  have hat : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hs := source_unitary_beta_core_special h hB hS d hc hb hcomm hbc hac Ma hm mark
  have hI := (source_unitary_neighbor_core_center_from_marking h hB hS d hc hb hcomm Ma hm mark).1
  have hz := source_unitary_remote_layer_eq_bot h hB hS d hc hb hcomm hbc hac Ma hm mark g hga hgb hesc
  rw [hI] at hz
  apply normal_subgroup_of_special_disjoint_center
    (neighborCoreIntersection (family P) a) (Q (family P) b) (Z (family P) b)
    (neighborCoreIntersection_le _ hab.symm)
  · exact ((source_Z_Q_U h b).2.trans
      ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)).trans
        (neighborCoreIntersection_normalized _ a)
  · exact hs.2.1.le
  · exact hs.1
  · apply bot_unique
    rw [inf_comm] at hz
    exact (inf_le_inf (neighborCoreIntersection_le _ hat.symm) le_rfl).trans hz.le



end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
