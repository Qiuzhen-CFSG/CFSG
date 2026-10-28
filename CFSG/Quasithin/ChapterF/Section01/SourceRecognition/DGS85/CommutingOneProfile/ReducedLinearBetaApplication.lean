module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearBetaCenters
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Arbitrary linear source cores under the original inclusion

Two genuine PSL2(2^n), PSL2(2^m) markings give I_beta = Z_beta,
Q_alpha = Z_alpha and Q_beta = V_beta on the reduced source graph.
The Frattini and derived layers coincide and are nontrivial and central;
Q_beta/Z_beta is elementary of order (2^n)^2. The complete beta-core and
edge-core centers both equal Z_beta, and the literal seed centralizes
only itself inside Q_beta.

These applications retain both fields, all original subgroup images and
their induced quotient isomorphisms. The edge-core order is exactly
2^m (2^n)^2 |Z_beta|. Thus the source center order and field relation remain
explicit mathematical obligations; this module does not assert the full
(11.7) numerical or path conclusions. Earlier local data and the actual
linear branch markings remain inputs; ambient finiteness is not required.

Source: DGS85, Groups and Graphs (1985), (11.6)(a), (11.7)(e),
pp.172--175; original-to-reduced construction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
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

/-- The literal source core profile for two arbitrary linear field markings.
This proves the core clauses of (11.7); field and center orders are retained. -/
theorem reduced_linear_linear_core_structure (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m)) :
    neighborCoreIntersection F₀ b = Z F₀ b ∧ Q F₀ a = Z F₀ a ∧
      Q F₀ b = pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b) ∧
      betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      (frattini (Q F₀ b)).map (Q F₀ b).subtype = ⁅Q F₀ b,Q F₀ b⁆ ∧
      ⁅Q F₀ b,Q F₀ b⁆ ≠ ⊥ ∧ ⁅Q F₀ b,Q F₀ b⁆ ≤ Z F₀ b ∧
      ⁅⁅Q F₀ b,Q F₀ b⁆,Q F₀ b⁆ = ⊥ := by
  obtain ⟨k,hk,hfin,hchar,_,⟨ea⟩⟩ := linear_coordinates_card ha
  obtain ⟨k',hk',hfin',hchar',_,⟨eb⟩⟩ := linear_coordinates_card hbmodel
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  exact ⟨source_linear_linear_neighbor_intersection_eq_center ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea (.linear m hm hbmodel) eb,
    source_linear_linear_core_eq_center ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea (.linear m hm hbmodel) eb,
    source_linear_linear_beta_core_structure ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea (.linear m hm hbmodel) eb⟩

/-- The exact linear-row seed, core and edge-core counts before the remaining
center-order and field-relation arguments. -/
theorem reduced_linear_linear_local_orders (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m)) :
    Nat.card (Z F₀ a ⊓ Q F₀ b : Subgroup G₀) = 2^n * Nat.card (Z F₀ b) ∧
      Nat.card (Z F₀ a) = 2^m * 2^n * Nat.card (Z F₀ b) ∧
      Nat.card (Q F₀ b) = (2^n)^2 * Nat.card (Z F₀ b) ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) =
        2^m * (2^n)^2 * Nat.card (Z F₀ b) := by
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  obtain ⟨k',hk',hfin',hchar',hcard',⟨eb⟩⟩ := linear_coordinates_card hbmodel
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hz := source_linear_linear_center_card_ratio ht hB d hc hb hcomm hbc hac
    (.linear n hn ha) ea (.linear m hm hbmodel) eb
  have hq := source_linear_linear_core_card_ratio ht hB d hc hb hcomm hbc hac
    (.linear n hn ha) ea (.linear m hm hbmodel) eb
  rw [hcard,hcard'] at hz hq
  exact ⟨hz.1,hz.2,hq⟩

/-- Both complete centers and the self-centralizing seed are constructed
from the actual arbitrary-field reduced graph. -/
theorem reduced_linear_linear_centers (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m)) :
    centerIn (Q F₀ b) = Z F₀ b ∧
      centerIn ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = Z F₀ b ∧
      Q F₀ b ⊓ centralizer (Z F₀ a ⊓ Q F₀ b : Set G₀) = Z F₀ a ⊓ Q F₀ b := by
  obtain ⟨k,hk,hfin,hchar,_,⟨ea⟩⟩ := linear_coordinates_card ha
  obtain ⟨k',hk',hfin',hchar',_,⟨eb⟩⟩ := linear_coordinates_card hbmodel
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  exact ⟨source_linear_linear_core_center ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea (.linear m hm hbmodel) eb,
    source_linear_linear_edge_center ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea (.linear m hm hbmodel) eb,
    source_linear_linear_seed_centralizer ht hB d hc hb hcomm hbc hac
      (.linear n hn ha) ea (.linear m hm hbmodel) eb⟩

/-- The literal quotient Q_beta/Z_beta has order q_alpha squared and is
elementary, for arbitrary positive degrees of both linear endpoint fields. -/
theorem reduced_linear_linear_core_quotient (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m)) :
    ∃ hN : ((Z F₀ b).subgroupOf (Q F₀ b)).Normal,
      letI := hN
      Nat.card (Q F₀ b ⧸ (Z F₀ b).subgroupOf (Q F₀ b)) = (2^n)^2 ∧
        IsElementaryAbelian 2 (Q F₀ b ⧸ (Z F₀ b).subgroupOf (Q F₀ b)) := by
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  obtain ⟨k',hk',hfin',hchar',_,⟨eb⟩⟩ := linear_coordinates_card hbmodel
  obtain ⟨hN,hsize,helem⟩ := source_linear_linear_core_quotient (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac
    (.linear n hn ha) ea (.linear m hm hbmodel) eb
  refine ⟨hN,?_,helem⟩
  rw [hcard] at hsize
  exact hsize

/-- Source (11.7)(e) and its core order ratios on the original subgroup
images, with the quotient markings transported through the same inclusion. -/
theorem original_reduced_linear_linear_cores (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) 2 (2 ^ m)) :
    (neighborCoreIntersection F₀ b).map (G₀).subtype = (Z F₀ b).map (G₀).subtype ∧
      (Q F₀ a).map (G₀).subtype = (Z F₀ a).map (G₀).subtype ∧
      (Q F₀ b).map (G₀).subtype = pairSpan ((Z F₀ a).map (G₀).subtype)
        ((Z F₀ c).map (G₀).subtype) ((Q F₀ b).map (G₀).subtype) ∧
      ⁅(Q F₀ b).map (G₀).subtype,(Q F₀ b).map (G₀).subtype⁆ ≠ ⊥ ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) = (2^n)^2 * Nat.card ((Z F₀ b).map (G₀).subtype) ∧
      Nat.card (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) =
        2^m * (2^n)^2 * Nat.card ((Z F₀ b).map (G₀).subtype) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := reduced_linear_linear_core_structure h d hc hb hcomm hbc hac n m hn hm
    (ha.of_mulEquiv eqa) (hbmodel.of_mulEquiv eqb)
  have ho := reduced_linear_linear_local_orders h d hc hb hcomm hbc hac n m hn hm
    (ha.of_mulEquiv eqa) (hbmodel.of_mulEquiv eqb)
  refine ⟨congrArg (map (G₀).subtype) hs.1,congrArg (map (G₀).subtype) hs.2.1,?_,?_,?_,?_⟩
  · have he := congrArg (map (G₀).subtype) hs.2.2.1
    simpa only [pairSpan,Subgroup.map_sup,map_inf _ _ _ (G₀).subtype_injective] using he
  · rw [←map_commutator]
    intro he
    apply hs.2.2.2.2.2.1
    exact (map_injective (G₀).subtype_injective) (he.trans (Subgroup.map_bot _).symm)
  · simpa only [card_map_of_injective (G₀).subtype_injective] using ho.2.2.1
  · simpa only [card_map_of_injective (G₀).subtype_injective] using ho.2.2.2

/-- The full centers retain their literal original-group images and both
original quotient markings. No ambient finiteness hypothesis is added. -/
theorem original_reduced_linear_linear_centers (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) 2 (2 ^ m)) :
    centerIn ((Q F₀ b).map (G₀).subtype) = (Z F₀ b).map (G₀).subtype ∧
      centerIn (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) =
        (Z F₀ b).map (G₀).subtype := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨hQ,hE,_⟩ := reduced_linear_linear_centers h d hc hb hcomm hbc hac n m hn hm
    (ha.of_mulEquiv eqa) (hbmodel.of_mulEquiv eqb)
  have hmap (Q : Subgroup G₀) : (centerIn Q).map (G₀).subtype = centerIn (Q.map (G₀).subtype) := by
    rw [centerIn_eq_map_center,centerIn_eq_map_center,map_embeddedCenter Q _ (G₀).subtype_injective]
  exact ⟨(hmap _).symm.trans (congrArg (map (G₀).subtype) hQ),
    (hmap _).symm.trans (congrArg (map (G₀).subtype) hE)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
