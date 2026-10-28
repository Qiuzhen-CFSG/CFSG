module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceFieldParameters
public import Theory.Representation.SL2.MinimalBinaryDegree
/-!
# Minimality of the original alpha center

The source field equation and center order make Z_alpha attain the minimum
nontrivial binary degree of its actual SL₂ actor. The original centerless
local action has no fixed vectors, so the minimum-degree lemma makes it
irreducible. The subgroup statement retains the literal conjugation action
and relative normalizer. AlphaFrattini uses it on Φ(Q_alpha) ∩ Z_alpha.
Source: DGS85, Groups and Graphs (1985), (5.7), (11.1), (11.6), (11.8),
printed pp.108,167,172--176.
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

theorem source_alpha_center_minimal_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    ∀ Y : Subgroup G, Y ≤ Z (family P) a →
      d.localGroup a ≤ normalizer (Y : Set G) → Y = ⊥ ∨ Y = Z (family P) a := by
  obtain ⟨hfield,n,hn,hi,hq⟩ := source_field_parameters_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have ho := (source_center_seed_pair_orders_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).2.2.1
  have hsize : Nat.card (Z (family P) a) = 2^(2*n) := by
    rw [←hfield,←hq,←pow_two,←pow_mul] at ho
    simpa only [Nat.mul_comm n 2] using ho
  exact center_minimal_of_degree h d hc hb hcomm (ea.trans ep.symm) n (by omega) hk hsize
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
