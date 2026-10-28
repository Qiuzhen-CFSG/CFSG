module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreProductIndex
public import Theory.SpecificGroups.SU3.SylowOmegaIndex
public import Theory.SpecificGroups.Suzuki.SylowOmegaIndex

/-!
# The characteristic-two order comparison for the Chapter 11 core product

CoreProductIndex identifies t=|S:Q_alpha Q_beta| with the index of the
alpha Sylow omega-center and bounds it above by the corresponding beta
index. In the complete rank-one catalogue these indices are 1, q for
Suzuki, and q² for either unitary cover, including every small parameter.
If q_beta²≤q_alpha, a nonlinear alpha is impossible: the only possible
boundary equality would make a Suzuki field order a square, contrary to
its odd exponent. Thus t=1, proving the core product.

The precise remaining (11.3)(g) input is stated as an inequality between
the literal critical-center and opposite-seed relative indices. It has not
been inferred from a linear-alpha formula. The actual alpha-selection
consumer uses the already proved pair-core span; the original application
transports both indices, both catalogue markings and the full edge core
through the reduction inclusion. General (11.3)(g), the nonelementary
profile and the final source assembly remain to be discharged by this owner.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(c,g,h), (11.4)--(11.5), printed pp.169--172.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups

private theorem omega_card_index_transport {H D : Type*} [Group H] [Group D] [Finite H]
    (e : H ≃* D) (T : Sylow 2 H) :
    let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
    Nat.card (omegaCenterIn (U : Subgroup D)) = Nat.card (omegaCenterIn (T : Subgroup H)) ∧
      (omegaCenterIn (U : Subgroup D)).relIndex U = (omegaCenterIn (T : Subgroup H)).relIndex T := by
  dsimp only
  change Nat.card (omegaCenterIn ((T : Subgroup H).map e.toMonoidHom)) = _ ∧
    (omegaCenterIn ((T : Subgroup H).map e.toMonoidHom)).relIndex
      ((T : Subgroup H).map e.toMonoidHom) = _
  rw [←NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,
    card_map_of_injective e.injective,relIndex_map_map_of_injective _ _ e.injective]
  exact ⟨rfl,rfl⟩

private theorem elementary_omega_index {H : Type*} [Group H]
    (T : Subgroup H) [IsElementaryAbelian 2 T] : (omegaCenterIn T).relIndex T = 1 := by
  have he : omegaCenterIn T = T := by
    apply le_antisymm (map_subtype_le _)
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hx,
      fun y hy => congrArg Subtype.val (mul_comm (⟨y,hy⟩ : T) (⟨x,hx⟩ : T)),
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  rw [he,relIndex_self]

private theorem omega_index_cases {H : Type*} [Group H]
    (M : IsRankOneModel H) (T : Sylow 2 H) :
    (omegaCenterIn (T : Subgroup H)).relIndex T = 1 ∨
      (∃ m, Nat.card (omegaCenterIn (T : Subgroup H)) = 2^(2*m+1) ∧
        (omegaCenterIn (T : Subgroup H)).relIndex T = 2^(2*m+1)) ∨
      (∃ n, 0 < n ∧ Nat.card (omegaCenterIn (T : Subgroup H)) = 2^n ∧
        (omegaCenterIn (T : Subgroup H)).relIndex T = (2^n)^2) := by
  let : Finite H := M.finite
  cases M with
  | linear n hn he =>
    let := linear_model_sylow_elementary he T
    exact Or.inl (elementary_omega_index (T : Subgroup H))
  | dihedral he =>
    let := dihedral_model_sylow_elementary he.some T
    exact Or.inl (elementary_omega_index (T : Subgroup H))
  | suzuki m he =>
    obtain ⟨e⟩ := he
    obtain ⟨hc,hi⟩ := omega_card_index_transport e T
    obtain ⟨hcard,hidx⟩ := suzukiSylow_omegaCenter_card_index m
      (T.mapSurjective (f := e.toMonoidHom) e.surjective)
    exact Or.inr (Or.inl ⟨m,hc.symm.trans hcard,hi.symm.trans hidx⟩)
  | projective_unitary n hn he =>
    obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := he
    obtain ⟨hc,hi⟩ := omega_card_index_transport e T
    obtain ⟨hcard,hidx⟩ := HermitianForm.SylowOmegaIndex.projective J hn hcard hconj
      (T.mapSurjective (f := e.toMonoidHom) e.surjective)
    exact Or.inr (Or.inr ⟨n,hn,hc.symm.trans hcard,hi.symm.trans hidx⟩)
  | special_unitary n hn he =>
    obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := he
    obtain ⟨hc,hi⟩ := omega_card_index_transport e T
    obtain ⟨hcard,hidx⟩ := HermitianForm.SylowOmegaIndex.special J hn hcard hconj
      (T.mapSurjective (f := e.toMonoidHom) e.surjective)
    exact Or.inr (Or.inr ⟨n,hn,hc.symm.trans hcard,hi.symm.trans hidx⟩)

private theorem omega_index_one_of_square_bound {H D : Type*} [Group H] [Group D]
    (Ma : IsRankOneModel H) (Mb : IsRankOneModel D) (Ta : Sylow 2 H) (Tb : Sylow 2 D)
    (hindex : (omegaCenterIn (Ta : Subgroup H)).relIndex Ta ≤
      (omegaCenterIn (Tb : Subgroup D)).relIndex Tb)
    (hbound : Nat.card (omegaCenterIn (Tb : Subgroup D))^2 ≤
      Nat.card (omegaCenterIn (Ta : Subgroup H))) :
    (omegaCenterIn (Ta : Subgroup H)).relIndex Ta = 1 := by
  rcases omega_index_cases Ma Ta with hlin | ⟨m,ha,hta⟩ | ⟨n,hn,ha,hta⟩
  · exact hlin
  · have hqa : 1 < 2^(2*m+1) := one_lt_pow₀ (by decide) (by omega)
    rcases omega_index_cases Mb Tb with hlin | ⟨k,hb,htb⟩ | ⟨k,hk,hb,htb⟩
    · rw [hta,hlin] at hindex
      omega
    · have hqb : 1 < 2^(2*k+1) := one_lt_pow₀ (by decide) (by omega)
      rw [hta,htb] at hindex
      rw [ha,hb] at hbound
      nlinarith
    · rw [hta,htb] at hindex
      rw [ha,hb] at hbound
      have he := le_antisymm hindex hbound
      rw [←pow_mul] at he
      have hh := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he
      omega
  · have hqa : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
    rcases omega_index_cases Mb Tb with hlin | ⟨k,hb,htb⟩ | ⟨k,hk,hb,htb⟩
    · rw [hta,hlin] at hindex
      nlinarith
    · have hqb : 1 < 2^(2*k+1) := one_lt_pow₀ (by decide) (by omega)
      rw [hta,htb] at hindex
      rw [ha,hb] at hbound
      nlinarith
    · rw [hta,htb] at hindex
      rw [ha,hb] at hbound
      nlinarith

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
open SimpleGraph SimpleGraph.PathTransitivePolygon

/-- The even-characteristic order comparison in (11.4), with its remaining
(11.3)(g) bound stated on the literal critical-center and opposite-seed indices.
No endpoint has been selected as linear. -/
theorem source_core_product_of_seed_square_bound_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hbound : ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b := by
  obtain ⟨Ta,Tb,hidx,hupper,hacard,hbcard⟩ :=
    source_core_product_indices_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hb' hc'
  have hindex := omega_index_one_of_square_bound Ma Mb Ta Tb (hidx ▸ hupper)
    (by simpa only [hacard,hbcard] using hbound)
  have hi : (Q (family P) a ⊔ Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = 1 := hidx.trans hindex
  have hab := source_critical_one_adjacent hc hb
  exact le_antisymm (relIndex_eq_one.mp hi) (sup_le (Noncommuting.graph_Q_le_edgeCore h hab)
    (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm))

/-- Actual alpha selection after the source order comparison, for every beta
row. The only extra numerical premise is precisely the earlier seed bound. -/
theorem source_alpha_linear_of_seed_square_bound_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hbound : ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) := by
  exact source_alpha_linear_of_core_identities h hB d hc hb hcomm hbc hac Ma Mb
    (source_core_product_of_seed_square_bound_on_path h hB d hc hb hbc hac Ma Mb hbound ht p hp ha hb' hc')
    (source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hb' hc')
section Original
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The source comparison and alpha marking in the original completion.
Both catalogue inputs and both indices use the original subgroup images;
the reduction inclusion is retained in the output core identity. -/
theorem original_reduced_core_product_and_alpha_of_seed_square_bound_on_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (hbound : (((Q F₀ b).map (G₀).subtype).relIndex ((Z F₀ a).map (G₀).subtype))^2 ≤
      ((Q F₀ a).map (G₀).subtype).relIndex
        ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    (((stabilizer F₀ a).map (G₀).subtype) ⊓
      ((stabilizer F₀ b).map (G₀).subtype)).pCoreIn 2 =
      (Q F₀ a).map (G₀).subtype ⊔ (Q F₀ b).map (G₀).subtype ∧
    ∃ n, 1 < n ∧ ClassicalGroup.IsPSL
      ((d.localGroup a).map (G₀).subtype ⧸ pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^n) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hbound₀ : ((Q F₀ b).relIndex (Z F₀ a))^2 ≤
      (Q F₀ a).relIndex (Z F₀ c ⊓ Q F₀ b) := by
    rwa [←map_inf _ _ _ (G₀).subtype_injective,
      relIndex_map_map_of_injective _ _ (G₀).subtype_injective,
      relIndex_map_map_of_injective _ _ (G₀).subtype_injective] at hbound
  have hproduct := source_core_product_of_seed_square_bound_on_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      hbound₀ ht p hp ha hb' hc'
  constructor
  · have hm := congrArg (Subgroup.map (G₀).subtype) hproduct
    rw [map_pCoreIn_of_injective 2 _ _ (G₀).subtype_injective,
      map_inf _ _ _ (G₀).subtype_injective,Subgroup.map_sup] at hm
    exact hm
  · obtain ⟨n,hn,hmark⟩ := source_alpha_linear_of_core_identities (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
        hproduct (source_rankOne_pair_core_span_on_path (Reduction.reduced_triple h)
          (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
            ht p hp ha hb' hc')
    exact ⟨n,hn,hmark.of_mulEquiv eqa.symm⟩
end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

