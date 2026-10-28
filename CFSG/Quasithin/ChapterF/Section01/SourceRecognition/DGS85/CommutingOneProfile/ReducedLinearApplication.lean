module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.DihedralCoreGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedRankOneApplication

/-!
# The linear Chapter 11 core identities in the reduced source geometry

The actual linear constructors of the earlier local quotient catalogue
supply matrix coordinates over their own characteristic-two fields. The
linear core-generation argument proves (11.4) for a linear alpha and any
beta rank-one model, and proves (11.3)(h) when beta is linear or dihedral-ten.
The existing neighbor-separation consumer then receives both proved core
identities, derives the (11.5) supplement, and proves the (11.6) separation
in the reduced completion and under its literal original inclusion.

These are applications to the linear branches of the earlier catalogue,
not a restriction of that catalogue. The remaining beta cases, the complete
(11.7)--(11.8) profiles and the marked recognition remain obligations of
this source family. No full-kernel/two-core identification is used.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.6), printed pp.169--174; reduction, printed pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

private theorem linear_coordinates {H : Type*} [Group H] {n : ℕ}
    (hM : ClassicalGroup.IsPSL H 2 (2 ^ n)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2), Nonempty (H ≃* SL(2,k)) := by
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := hM
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact ⟨k,hk,hfin,inferInstance,⟨e.trans f.symm⟩⟩

/-- The linear alpha constructor discharges the edge-product premise in the original reduced geometry. -/
theorem reduced_linear_edge_core_product (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 = Q F₀ a ⊔ Q F₀ b := by
  obtain ⟨k,hk,hfin,hchar,⟨e⟩⟩ := linear_coordinates ha
  exact source_linear_edge_core_product (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (.linear n hn ha) Mb e

/-- The two actual linear constructors discharge both source core identities, without extra generation hypotheses. -/
theorem reduced_linear_core_identities (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m)) :
    (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 = Q F₀ a ⊔ Q F₀ b ∧
      Q F₀ b = pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b) ⊔ (Q F₀ a ⊓ Q F₀ b) := by
  obtain ⟨k,hk,hfin,hchar,⟨ea⟩⟩ := linear_coordinates ha
  obtain ⟨k',hk',hfin',hchar',⟨eb⟩⟩ := linear_coordinates hbmodel
  exact ⟨source_linear_edge_core_product (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac
      (.linear n hn ha) (.linear m hm hbmodel) ea,
    source_linear_pair_core_generation (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac
      (.linear n hn ha) (.linear m hm hbmodel) ea eb⟩

/-- The literal earlier consumer now needs no Chapter 11 core-generation premises in the linear branch. -/
theorem reduced_linear_neighbor_separation (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    (∀ v, (graph F₀).Adj a v →
      ∃ w ∈ (Z F₀ c ⊓ Q F₀ b) ⊔ (Z F₀ (g • c) ⊓ Q F₀ (g • b)), w • b = v) ∧
      neighborCoreIntersection F₀ b ⊓ Q F₀ (g • c) = ⊥ ∧
      (neighborCoreIntersection F₀ b).map (G₀).subtype ⊓ (Q F₀ (g • c)).map (G₀).subtype = ⊥ := by
  obtain ⟨hproduct,hcore⟩ := reduced_linear_core_identities h d hc hb hbc hac n m hn hm ha hbmodel
  exact reduced_rankOne_neighbor_separation h d hc hb hbc hac
    (.linear n hn ha) (.linear m hm hbmodel) hproduct hcore g hga hgb

/-- The dihedral beta candidate also feeds the literal separation consumer with both core premises proved. -/
theorem reduced_linear_dihedral_neighbor_separation (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    (∀ v, (graph F₀).Adj a v →
      ∃ w ∈ (Z F₀ c ⊓ Q F₀ b) ⊔ (Z F₀ (g • c) ⊓ Q F₀ (g • b)), w • b = v) ∧
      neighborCoreIntersection F₀ b ⊓ Q F₀ (g • c) = ⊥ ∧
      (neighborCoreIntersection F₀ b).map (G₀).subtype ⊓ (Q F₀ (g • c)).map (G₀).subtype = ⊥ := by
  obtain ⟨k,hk,hfin,hchar,⟨ea⟩⟩ := linear_coordinates ha
  have hproduct := source_linear_edge_core_product (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (.linear n hn ha) (.dihedral ⟨eb⟩) ea
  have hcore := source_linear_dihedral_pair_core_generation (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (.linear n hn ha) ea eb
  exact reduced_rankOne_neighbor_separation h d hc hb hbc hac
    (.linear n hn ha) (.dihedral ⟨eb⟩) hproduct hcore g hga hgb

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
