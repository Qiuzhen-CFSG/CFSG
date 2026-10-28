module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryBetaCenterBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedDihedralExclusion

/-!
# Field selection and the source profiles in the original reduced geometry

Every actual PSL2(2^n)/SL2(2) branch has n=2 and |Z_beta|=2. The original
reduced-Borel construction makes the alpha actor the full stabilizer, and
thickness supplies the turns needed by the module argument. Applying the
existing field-four profile gives the literal core orders 16 and 32 and
edge-core order 64. For finite completions it also gives r=4, s=5 and odd
long-path fixers, now without a supplied field-four marking.

The same field selection applies to every linear-alpha/D10-beta candidate;
the previously proved actual-core obstruction therefore excludes that row.
Both conclusions retain quotient markings on the literal original images
and transport through the original reduced-group inclusion. The earlier
local inputs remain explicit. General alpha-row selection, the other beta
fields, and the remaining unitary profiles are further source obligations.

Source: DGS85, (11.6)--(11.7), pp.172--175, and reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

private theorem source_turns (h : HypothesisF11 L S)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b) (hb : DGS85.b F₀ = 1) :
    ∃ c, (graph F₀).Adj b c ∧ a ≠ c ∧
      ∃ g : G₀, g ∈ stabilizer F₀ a ∧ g • b ≠ b := by
  have ht := Reduction.reduced_triple h
  have hS := Reduction.reduced_vertex_sylow h
  have hval (v : Vertex F₀) : 3 ≤ Nat.card ((graph F₀).neighborSet v) := by
    rw [card_neighbors_of_indices F₀ (fun i => ((F₀ (!i)).subgroupOf (F₀ i)).index) (fun _ => rfl)]
    exact source_valence_ge_three ht hS v.type
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F₀).neighborSet b)
    (by rw [←Nat.card_coe_set_eq]; have hh := hval b; omega) a
  obtain ⟨b',hab',hb'b⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F₀).neighborSet a)
    (by rw [←Nat.card_coe_set_eq]; have hh := hval a; omega) b
  obtain ⟨g,hga,hgb'⟩ := locally_transitive F₀ (source_critical_one_adjacent hc hb) hab'
  exact ⟨c,hbc,hca.symm,g,hga,by rw [hgb']; exact hb'b⟩

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


private theorem binary_rankOne {H : Type*} [Group H] (e : H ≃* SL(2,ZMod 2)) :
    IsRankOneModel H := by
  let f : SL(2,ZMod 2) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (ZMod 2))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact .linear 1 (by decide) ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e.trans f⟩⟩

/-- The actual source center and escaping residual layer satisfy the uniform
bounds, with no full-alpha mark, chosen turn or center order as an input. -/
theorem reduced_linear_binary_center_bounds (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    Nat.card (Z F₀ b) ≤ 2^n ∧
      ∃ t ∈ stabilizer F₀ a, t • b ≠ b ∧ ¬ Z F₀ b ≤ Q F₀ (t • b) ∧
        2 * Nat.card (Z F₀ b ⊓ Q F₀ (t • b) : Subgroup G₀) ≤ 2^n := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := source_turns h hc hb
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  let eL := MulEquiv.subgroupCongr
    (reduced_binary_alpha_local_eq_full h d (source_critical_one_adjacent hc hb) eb).symm
  let ef := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans ea
  have hbound := source_linear_binary_center_card_le_field ht hB hS d hc hb hcomm hbc hac
    (.linear n hn ha) ea ef eb n hn hcard g hga hgb
  obtain ⟨t,hta,htb,hesc⟩ := source_linear_rankOne_center_escape ht hB d hc hb hcomm hbc hac
    (.linear n hn ha) (binary_rankOne eb) ea g hga hgb
  have hlayer := source_linear_binary_escape_layer_bound ht hB hS d hc hb hcomm hbc hac
    (.linear n hn ha) ea ef eb n hn hcard t hta htb hesc
  exact ⟨hcard ▸ hbound,t,hta,htb,hesc,hcard ▸ hlayer⟩

/-- The uniform parameter restrictions preserve the original subgroup images
and the same escaping turn in the actual reduced graph. -/
theorem original_reduced_linear_binary_center_bounds (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SL(2,ZMod 2)) :
    Nat.card ((Z F₀ b).map (G₀).subtype) ≤ 2^n ∧
      ∃ t ∈ stabilizer F₀ a, t • b ≠ b ∧
        ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (t • b)).map (G₀).subtype ∧
        2 * Nat.card ((Z F₀ b).map (G₀).subtype ⊓
          (Q F₀ (t • b)).map (G₀).subtype : Subgroup G) ≤ 2^n := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  obtain ⟨hbound,t,hta,htb,hesc,hlayer⟩ := reduced_linear_binary_center_bounds h d hc hb hcomm
    n hn (ha.of_mulEquiv eqa) (eqb.trans eb)
  refine ⟨?_,t,hta,htb,?_,?_⟩
  · simpa only [card_map_of_injective (G₀).subtype_injective] using hbound
  · exact fun he => hesc ((map_le_map_iff_of_injective (G₀).subtype_injective).mp he)
  · simpa only [←Subgroup.map_inf _ _ _ (G₀).subtype_injective,
      card_map_of_injective (G₀).subtype_injective] using hlayer

/-- The full arbitrary linear-alpha/binary-beta branch selects the alpha
field of order four and beta center of order two. -/
theorem reduced_linear_binary_parameter_two (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    n = 2 ∧ Nat.card (Z F₀ b) = 2 := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := source_turns h hc hb
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  let eL := MulEquiv.subgroupCongr
    (reduced_binary_alpha_local_eq_full h d (source_critical_one_adjacent hc hb) eb).symm
  let ef := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans ea
  exact source_linear_binary_parameter_two (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    d hc hb hcomm hbc hac (.linear n hn ha) ea ef eb n hn hcard g hga hgb

/-- The literal binary-beta core profile now has no field-four selection
premise. This discharges the numerical and core clauses of (11.7) in this row. -/
theorem reduced_linear_binary_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    n = 2 ∧ Q F₀ a = Z F₀ a ∧ betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      Nat.card (Z F₀ b) = 2 ∧ Nat.card (Z F₀ a) = 16 ∧
      Nat.card (Q F₀ b) = 32 ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = 64 := by
  have hn2 := (reduced_linear_binary_parameter_two h d hc hb hcomm n hn ha eb).1
  have ha4 : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4 := by
    simpa only [hn2,show 2^2 = 4 by decide] using ha
  exact ⟨hn2,reduced_linear_four_binary_profile h d hc hb hcomm ha4 eb⟩

/-- The D10 beta candidate is excluded for every alpha linear field,
with the actual reduced full-alpha marking derived from the source. -/
theorem reduced_linear_dihedral_exclusion (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) : False := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := source_turns h hc hb
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  let eL := MulEquiv.subgroupCongr
    (reduced_dihedral_alpha_local_eq_full h d (source_critical_one_adjacent hc hb) eb).symm
  let ef := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans ea
  have hp := source_linear_dihedral_parameter_two (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    d hc hb hcomm hbc hac (.linear n hn ha) ea ef eb n hn hcard g hga hgb
  apply reduced_linear_four_dihedral_exclusion h d hc hb hcomm _ eb
  simpa only [hp.1,show 2^2 = 4 by decide] using ha

/-- The selected binary-beta orders on the actual original-group images,
with the alpha field parameter retained and proved to be two. -/
theorem original_reduced_linear_binary_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SL(2,ZMod 2)) :
    n = 2 ∧ Nat.card ((Z F₀ b).map (G₀).subtype) = 2 ∧
      Nat.card ((Q F₀ a).map (G₀).subtype) = 16 ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) = 32 ∧
      Nat.card (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) = 64 := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  obtain ⟨hn2,hQa,_,hZb,hZa,hQb,hE⟩ := reduced_linear_binary_profile h d hc hb hcomm
    n hn (ha.of_mulEquiv eqa) (eqb.trans eb)
  simpa only [card_map_of_injective (G₀).subtype_injective,hQa] using ⟨hn2,hZb,hZa,hQb,hE⟩

/-- The linear/D10 exclusion uses the original images and their induced
quotient equivalences; no alpha field selection is assumed. -/
theorem original_reduced_linear_dihedral_exclusion (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* DihedralGroup 5) : False := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  exact reduced_linear_dihedral_exclusion h d hc hb hcomm n hn (ha.of_mulEquiv eqa) (eqb.trans eb)

open NoncommutingProfile Theory.GroupTheory.WeakBNPair.RegularTree

/-- The arbitrary linear/binary branch has the original r=4, s=5 and odd
long-path fixers after the literal inclusion into a finite completion. -/
theorem original_reduced_linear_binary_path_profile [Finite G]
    (h : HypothesisF11 L S) (d : EarlierLocalTheorems F₀)
    (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2 ^ n))
    (eb : ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) ≃* SL(2,ZMod 2)) :
    n = 2 ∧ HasSourcePathParameters (P := fun i => (Reduction.P₀ L S i).subgroupOf G₀) 4 5 ∧
      ∀ {a b : Vertex F₀} (p : (graph F₀).Walk a b), IsSourcePath p → 5 ≤ p.length →
        Odd (Nat.card ((pathFixer (X := G₀) p).map (G₀).subtype)) := by
  have hn2 := (original_reduced_linear_binary_profile h d hc hb hcomm n hn ha eb).1
  refine ⟨hn2,original_reduced_four_binary_path_profile h d hc hb hcomm ?_ eb⟩
  simpa only [hn2,show 2^2 = 4 by decide] using ha

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
