module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCenterEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphExclusions

/-!
# The remaining Chapter 11 layers in the original reduced completion

The actual alpha PSL₂ marking supplies the same characteristic-two field
and its stated cardinality. The general central-layer, nonquadratic-action
and center-escape proofs then apply to every beta catalogue row. These
applications preserve I_beta, all original cores and centers, the literal
pair span and its nontrivial derived/Frattini layer. The intersection,
centralization and escape statements are also transported under the actual
reduced-to-original inclusion, without identifying the full kernel with O₂.

The last theorem applies the existing literal D₁₀ exclusion. It discharges
pair-core generation, seed intersection and noncommutativity; Q_alpha =
Z_alpha, the center orders and the seed index remain explicit source inputs.
This does not claim the unconditional exclusion, alpha row selection, layer
vanishing, general center orders, unitary profiles or marked recognition.
Those remain obligations of the complete commuting-one source family.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(e,f,h), (11.5)--(11.7), printed pp.169--175; reduction, pp.95--96.
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

/-- The actual reduced source layer is elementary, bounded by the unchanged
alpha field parameter, centralizes the alpha core and equals the center-core intersection. -/
theorem reduced_linear_rankOne_layer_control (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    IsElementaryAbelian 2 (neighborCoreIntersection F₀ b ⊓ Q F₀ (g • b) : Subgroup G₀) ∧
      Nat.card (neighborCoreIntersection F₀ b ⊓ Q F₀ (g • b) : Subgroup G₀) ≤ 2^n ∧
      neighborCoreIntersection F₀ b ⊓ Q F₀ (g • b) ≤ centralizer (Q F₀ a : Set G₀) ∧
      neighborCoreIntersection F₀ b ⊓ Q F₀ (g • b) = Z F₀ b ⊓ Q F₀ (g • b) ∧
      Disjoint (Z F₀ b) (Z F₀ (g • b)) := by
  obtain ⟨k,hk,hfin,hchar,hcard,⟨e⟩⟩ := linear_coordinates_card ha
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hh := source_linear_rankOne_intersection_layer ht hB d hc hb hbc hac (.linear n hn ha) Mb e g hga hgb
  rw [hcard] at hh
  exact ⟨hh.1,hh.2,
    source_linear_rankOne_layer_centralizes_core ht hB d hc hb hbc hac (.linear n hn ha) Mb e g hga hgb,
    source_linear_rankOne_layer_eq_center_inf ht hB d hc hb hcomm hbc hac (.linear n hn ha) Mb e g hga hgb,
    source_linear_rankOne_beta_centers_disjoint ht hB d hc hb hcomm hbc hac (.linear n hn ha) Mb e g hga hgb⟩

/-- Nonquadratic seed action and nontrivial central derived/Frattini layer
on the same literal reduced geometry; no noncommutativity premise is added. -/
theorem reduced_linear_rankOne_nonquadratic_pair (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    ⁅⁅Z F₀ a,Z F₀ c ⊓ Q F₀ b⁆,Z F₀ c ⊓ Q F₀ b⁆ ≠ ⊥ ∧
      let V := pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)
      ⁅V,V⁆ ≠ ⊥ ∧ (frattini V).map V.subtype = ⁅V,V⁆ ∧
        ⁅V,V⁆ ≤ Z F₀ b ∧ ⁅⁅V,V⁆,V⁆ = ⊥ := by
  obtain ⟨k,hk,hfin,hchar,_,⟨e⟩⟩ := linear_coordinates_card ha
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  exact ⟨source_linear_rankOne_seed_nonquadratic ht hB d hc hb hcomm hbc hac (.linear n hn ha) Mb e,
    source_linear_rankOne_pair_nonabelian ht hB d hc hb hcomm hbc hac (.linear n hn ha) Mb e,
    source_linear_rankOne_pair_layers ht hB d hc hb hcomm hbc hac (.linear n hn ha) Mb e⟩

/-- Transport of the controlled layer and its centralization through the
original inclusion, preserving the actual intersection and core maps. -/
theorem reduced_linear_rankOne_layer_control_original (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    let J := (neighborCoreIntersection F₀ b).map (G₀).subtype ⊓ (Q F₀ (g • b)).map (G₀).subtype
    IsElementaryAbelian 2 J ∧ Nat.card J ≤ 2^n ∧
      J ≤ centralizer ((Q F₀ a).map (G₀).subtype : Set G) ∧
      J = (Z F₀ b).map (G₀).subtype ⊓ (Q F₀ (g • b)).map (G₀).subtype := by
  have hh := reduced_linear_rankOne_layer_control h d hc hb hcomm hbc hac n hn ha Mb g hga hgb
  let J₀ := neighborCoreIntersection F₀ b ⊓ Q F₀ (g • b)
  let : IsElementaryAbelian 2 J₀ := hh.1
  dsimp only
  rw [←map_inf _ _ _ (G₀).subtype_injective]
  refine ⟨IsElementaryAbelian.map (G₀).subtype,?_,?_,?_⟩
  · rw [card_map_of_injective (G₀).subtype_injective]
    exact hh.2.1
  · apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr hh.2.2.1,Subgroup.map_bot]
  · have hm := congrArg (map (G₀).subtype) hh.2.2.2.1
    exact hm.trans (map_inf _ _ _ (G₀).subtype_injective)

/-- Source center escape, under the original reduced-to-original inclusion.
The escaping center and the opposite core are not replaced by proxy subgroups. -/
theorem reduced_linear_rankOne_center_escape_original (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    ∃ t ∈ stabilizer F₀ a, t • b ≠ b ∧
      ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (t • b)).map (G₀).subtype := by
  obtain ⟨k,hk,hfin,hchar,_,⟨e⟩⟩ := linear_coordinates_card ha
  obtain ⟨t,hta,htb,ht⟩ := source_linear_rankOne_center_escape (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac (.linear n hn ha) Mb e g hga hgb
  exact ⟨t,hta,htb,fun he => ht ((map_le_map_iff_of_injective (G₀).subtype_injective).mp he)⟩

/-- Apply the existing literal D10 exclusion with pair-core generation,
noncommutativity and seed-intersection identity now discharged. The remaining
alpha-core and center-order assertions of (11.6)--(11.7) are explicit. -/
theorem reduced_linear_rankOne_dihedral_exclusion_of_center_orders (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (Lβ : Subgroup (stabilizer F₀ b))
    (hQa : Q F₀ a = Z F₀ a) (hZa : Nat.card (Z F₀ a) = 16)
    (hindex : (Z F₀ a ⊓ Q F₀ b).relIndex (Z F₀ a) = 2)
    (hZb : Nat.card (Z F₀ b) = 2) :
    ¬ Nonempty ((Lβ ⧸ (pCore 2 (stabilizer F₀ b)).subgroupOf Lβ) ≃* DihedralGroup 5) := by
  obtain ⟨k,hk,hfin,hchar,_,⟨e⟩⟩ := linear_coordinates_card ha
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hinter : Nat.card ((Z F₀ a ⊓ Q F₀ b) ⊓ (Z F₀ c ⊓ Q F₀ b) : Subgroup G₀) = 2 := by
    have hi : (Z F₀ a ⊓ Q F₀ b) ⊓ (Z F₀ c ⊓ Q F₀ b) = Z F₀ b :=
      (source_linear_rankOne_center_intersections ht hB d hc hb hcomm hbc hac
        (.linear n hn ha) Mb e).2.2.2
    rw [hi]
    exact hZb
  exact source_beta_quotient_not_dihedralTen ht (source_critical_one_adjacent hc hb) hbc Lβ
    (source_linear_rankOne_core_identities ht hB d hc hb hbc hac (.linear n hn ha) Mb e).2
    hQa hZa hindex hinter
    (source_linear_rankOne_pair_nonabelian ht hB d hc hb hcomm hbc hac (.linear n hn ha) Mb e)
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
