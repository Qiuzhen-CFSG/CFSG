module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.DihedralCores

/-!
# Dihedral-candidate core structure on the original reduced source

The literal alpha PSL2 marking supplies its characteristic-two field. In
the dihedral beta branch the source graph then gives I_beta = Z_beta,
Q_alpha = Z_alpha, Q_beta = V_beta, and the exact seed/core/Sylow counts
in terms of the still-undetermined beta center. The same identities and
orders are transported by the reduced-to-original inclusion.

The field-four dihedral exclusion now needs only |Z_beta| = 2 beyond the
earlier local data and candidate markings. The alpha-core equality,
seed index and orders, noncommutativity, and literal local quotient
comparison are proved. General row selection, beta-center order and
the remaining Chapter 11 profiles retain their source obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3), (11.6)--(11.7), printed pp.168--175; reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

private theorem linear_coordinates_card {H : Type*} [Group H] {n : ℕ}
    (hM : ClassicalGroup.IsPSL H 2 (2 ^ n)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      Nat.card k = 2^n ∧ Nonempty (H ≃* SL(2,k)) := by
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := hM
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact ⟨k,hk,hfin,inferInstance,hcard,⟨e.trans f.symm⟩⟩

/-- The actual dihedral candidate supplies all three source core identities
and the nontrivial central derived/Frattini layer. -/
theorem reduced_linear_dihedral_core_structure (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    neighborCoreIntersection F₀ b = Z F₀ b ∧ Q F₀ a = Z F₀ a ∧
      Q F₀ b = pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b) ∧
      betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      (frattini (Q F₀ b)).map (Q F₀ b).subtype = ⁅Q F₀ b,Q F₀ b⁆ ∧
      ⁅Q F₀ b,Q F₀ b⁆ ≠ ⊥ ∧ ⁅Q F₀ b,Q F₀ b⁆ ≤ Z F₀ b ∧
      ⁅⁅Q F₀ b,Q F₀ b⁆,Q F₀ b⁆ = ⊥ := by
  obtain ⟨k,hk,hfin,hchar,_,⟨ea⟩⟩ := linear_coordinates_card ha
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  exact ⟨source_linear_dihedral_neighbor_intersection_eq_center ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea eb g hga hgb,
    source_linear_dihedral_core_eq_center ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea eb g hga hgb,
    source_linear_dihedral_beta_core_structure ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea eb g hga hgb⟩

/-- The original alpha field parameter is retained in every source count;
the beta-center order is not assumed to be two. -/
theorem reduced_linear_dihedral_local_orders (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    (Z F₀ a ⊓ Q F₀ b).relIndex (Z F₀ a) = 2 ∧
      Nat.card (Z F₀ a ⊓ Q F₀ b : Subgroup G₀) = 2^n * Nat.card (Z F₀ b) ∧
      Nat.card (Z F₀ a) = 2 * 2^n * Nat.card (Z F₀ b) ∧
      Nat.card (Q F₀ b) = (2^n)^2 * Nat.card (Z F₀ b) ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) =
        2 * (2^n)^2 * Nat.card (Z F₀ b) := by
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hz := source_linear_dihedral_center_card_ratio ht hB d hc hb hcomm hbc hac
    (.linear n hn ha) ea eb
  have hq := source_linear_dihedral_core_card_ratio ht hB d hc hb hcomm hbc hac
    (.linear n hn ha) ea eb g hga hgb
  rw [hcard] at hz hq
  exact ⟨source_dihedral_seed_index ht d hc hb eb,hz.1,hz.2,hq⟩

/-- The same core identities and counts after the literal inclusion into
the original completion, including the actual two-seed subgroup. -/
theorem reduced_linear_dihedral_original_cores (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    (neighborCoreIntersection F₀ b).map (G₀).subtype = (Z F₀ b).map (G₀).subtype ∧
      (Q F₀ a).map (G₀).subtype = (Z F₀ a).map (G₀).subtype ∧
      (Q F₀ b).map (G₀).subtype = pairSpan ((Z F₀ a).map (G₀).subtype)
        ((Z F₀ c).map (G₀).subtype) ((Q F₀ b).map (G₀).subtype) ∧
      ⁅(Q F₀ b).map (G₀).subtype,(Q F₀ b).map (G₀).subtype⁆ ≠ ⊥ ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) = (2^n)^2 * Nat.card ((Z F₀ b).map (G₀).subtype) := by
  have hs := reduced_linear_dihedral_core_structure h d hc hb hcomm hbc hac n hn ha eb g hga hgb
  have ho := reduced_linear_dihedral_local_orders h d hc hb hcomm hbc hac n hn ha eb g hga hgb
  refine ⟨congrArg (map (G₀).subtype) hs.1,congrArg (map (G₀).subtype) hs.2.1,?_,?_,?_⟩
  · have hm := congrArg (map (G₀).subtype) hs.2.2.1
    simpa only [pairSpan,Subgroup.map_sup,map_inf _ _ _ (G₀).subtype_injective] using hm
  · rw [←map_commutator]
    intro he
    apply hs.2.2.2.2.2.1
    exact (map_injective (G₀).subtype_injective) (he.trans (Subgroup.map_bot _).symm)
  · simpa only [card_map_of_injective (G₀).subtype_injective] using ho.2.2.2.1

/-- The field-four dihedral candidate is impossible once its remaining
source beta-center order is two. No core, seed-order or noncommutativity
premise remains in this literal application. -/
theorem reduced_linear_four_dihedral_exclusion_of_center_order (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hZb : Nat.card (Z F₀ b) = 2) : False := by
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card (n := 2) ha
  exact source_linear_four_dihedral_exclusion_of_center_order (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (.linear 2 (by decide) ha)
    ea eb g hga hgb hcard hZb

/-- The original reduced quotient Q_beta/Z_beta is elementary of the exact
field-square order; both subgroups and its normal structure are retained. -/
theorem reduced_linear_dihedral_core_quotient (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    ∃ hN : ((Z F₀ b).subgroupOf (Q F₀ b)).Normal,
      letI := hN
      Nat.card (Q F₀ b ⧸ (Z F₀ b).subgroupOf (Q F₀ b)) = (2^n)^2 ∧
        IsElementaryAbelian 2 (Q F₀ b ⧸ (Z F₀ b).subgroupOf (Q F₀ b)) := by
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  obtain ⟨hN,hsize,helem⟩ := source_linear_dihedral_core_quotient (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (.linear n hn ha) ea eb g hga hgb
  refine ⟨hN,?_,helem⟩
  rw [hcard] at hsize
  exact hsize


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
