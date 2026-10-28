module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneCenterIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedRankOneApplication

/-!
# Every beta core identity in the original reduced Chapter 11 geometry

The actual linear alpha constructor supplies its characteristic-two matrix
coordinates. NonlinearCoreGeneration then proves (11.3)(h) and (11.4) for
all beta constructors of the earlier catalogue. Their literal application
to the existing separation consumer discharges both core premises, obtains
the (11.5) opposite-seed supplement, and gives the opening (11.6) vanishing
in the reduced completion and under its original subgroup inclusion.
The same source geometry also gives the mixed core-center intersections,
identifies them with Z_beta in the commuting branch, and retains the actual
pair span's central derived/Frattini layer.

The earlier local-group data and alpha row selection remain explicit. The
complete (11.7)--(11.8) profiles, exclusions and marked recognition are still
owned by this source family; this is not an exhaustive classification.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.6), printed pp.169--174; reduction, pp.95--96.
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

/-- The actual linear alpha constructor discharges both Chapter 11 core
 identities for every beta constructor in the original reduced geometry. -/
theorem reduced_linear_rankOne_core_identities (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 = Q F₀ a ⊔ Q F₀ b ∧
      Q F₀ b = pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b) ⊔ (Q F₀ a ⊓ Q F₀ b) := by
  obtain ⟨k,hk,hfin,hchar,⟨e⟩⟩ := linear_coordinates ha
  exact source_linear_rankOne_core_identities (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (.linear n hn ha) Mb e

/-- Apply the existing (11.6) consumer with both (11.3)(h) and (11.4)
 proved, retaining the literal inclusion into the original completion. -/
theorem reduced_linear_rankOne_neighbor_separation (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    (∀ v, (graph F₀).Adj a v →
      ∃ w ∈ (Z F₀ c ⊓ Q F₀ b) ⊔ (Z F₀ (g • c) ⊓ Q F₀ (g • b)), w • b = v) ∧
      neighborCoreIntersection F₀ b ⊓ Q F₀ (g • c) = ⊥ ∧
      (neighborCoreIntersection F₀ b).map (G₀).subtype ⊓ (Q F₀ (g • c)).map (G₀).subtype = ⊥ := by
  obtain ⟨hproduct,hcore⟩ := reduced_linear_rankOne_core_identities h d hc hb hbc hac n hn ha Mb
  exact reduced_rankOne_neighbor_separation h d hc hb hbc hac
    (.linear n hn ha) Mb hproduct hcore g hga hgb

/-- The literal mixed core-center identities do not need an alpha row
 selection; the original beta quotient alone supplies the pair movement. -/
theorem reduced_rankOne_mixed_center_intersections (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    Z F₀ a ⊓ Q F₀ c = Z F₀ a ⊓ Z F₀ c ∧
      Q F₀ a ⊓ Z F₀ c = Z F₀ a ⊓ Z F₀ c :=
  source_rankOne_mixed_center_intersections (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc Mb

/-- The preceding core identities now identify all four intersections and
 the central derived/Frattini layer of the actual pair span in the reduced graph. -/
theorem reduced_linear_rankOne_center_layers (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    Z F₀ a ⊓ Q F₀ c = Z F₀ b ∧ Q F₀ a ⊓ Z F₀ c = Z F₀ b ∧
      Z F₀ a ⊓ Z F₀ c = Z F₀ b ∧
      (Z F₀ a ⊓ Q F₀ b) ⊓ (Z F₀ c ⊓ Q F₀ b) = Z F₀ b ∧
      let V := pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)
      (frattini V).map V.subtype = ⁅V,V⁆ ∧ ⁅V,V⁆ ≤ Z F₀ b ∧ ⁅⁅V,V⁆,V⁆ = ⊥ := by
  obtain ⟨k,hk,hfin,hchar,⟨e⟩⟩ := linear_coordinates ha
  have hi := source_linear_rankOne_center_intersections (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (.linear n hn ha) Mb e
  exact ⟨hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,
    source_linear_rankOne_pair_layers (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (.linear n hn ha) Mb e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
