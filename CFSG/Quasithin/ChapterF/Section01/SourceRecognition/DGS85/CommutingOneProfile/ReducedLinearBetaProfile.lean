module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathExistence
public import Theory.GroupTheory.PCoreInRestriction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearBetaParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedLinearBetaApplication

/-!
# General linear (11.7) parameters on the original reduced graph

Source thickness supplies the alpha and beta turns needed for the module
argument. Genuine PSL2(2^n) and PSL2(2^m) markings then force n=2m and
|Z_beta|=2^m. Combining this with the proved core identities gives
Q_alpha=Z_alpha, Q_beta=V_beta, |Q_alpha|=q_alpha²,
|Q_beta|=q_alpha² q_beta and |S_0|=q_alpha² q_beta².

The original-image applications transport both quotient markings through
the same reduced-group inclusion. At the base edge the final theorem
identifies the image of its two-core with O2 of the full original Borel,
so the numerical (11.7)(c) conclusion applies to that literal Borel.
Only finite vertex stabilizers are required. Earlier local data and the
two genuine linear row markings remain explicit; general alpha-row
selection, the nonlinear branch and the remaining marked/path assembly
are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6)--(11.7), pp.172--175, and original reduction, pp.95--96.
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


/-- Source (11.6)--(11.7) field and center restrictions for arbitrary genuine
linear markings, with both required turns supplied by source thickness. -/
theorem reduced_linear_linear_parameters (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m)) :
    n = 2*m ∧ Nat.card (Z F₀ b) = 2^m := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := source_turns h hc hb
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  obtain ⟨k',hk',hfin',hchar',hcard',⟨eb⟩⟩ := linear_coordinates_card hbmodel
  exact source_linear_linear_parameters (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    d hc hb hcomm hbc hac (.linear n hn ha) ea (.linear m hm hbmodel) eb
    n m hn hm hcard hcard' g hga hgb

/-- The complete core and numerical clauses of the linear/linear (11.7) row.
In particular the original edge two-core has order q_alpha² q_beta². -/
theorem reduced_linear_linear_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2 ^ m)) :
    n = 2*m ∧ Q F₀ a = Z F₀ a ∧ betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      Nat.card (Z F₀ b) = 2^m ∧ Nat.card (Z F₀ a) = (2^n)^2 ∧
      Nat.card (Q F₀ b) = (2^n)^2 * 2^m ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = (2^n)^2 * (2^m)^2 := by
  obtain ⟨c,hbc,hac,_⟩ := source_turns h hc hb
  obtain ⟨hnm,hZ⟩ := reduced_linear_linear_parameters h d hc hb hcomm n m hn hm ha hbmodel
  have hs := reduced_linear_linear_core_structure h d hc hb hcomm hbc hac n m hn hm ha hbmodel
  obtain ⟨_,hZa,hQ,hE⟩ := reduced_linear_linear_local_orders h d hc hb hcomm hbc hac n m hn hm ha hbmodel
  have hfield : (2:ℕ)^n = (2^m)^2 := by rw [hnm,Nat.mul_comm 2 m,pow_mul]
  rw [hZ] at hZa hQ hE
  refine ⟨hnm,hs.2.1,hs.2.2.2.1,hZ,?_,hQ,?_⟩
  · rw [hZa,hfield]
    ring
  · rw [hE]
    ring

/-- The exact source parameter and Sylow orders preserve both original
quotient markings and every literal reduced-to-original subgroup inclusion. -/
theorem original_reduced_linear_linear_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) 2 (2 ^ m)) :
    n = 2*m ∧ (Q F₀ a).map (G₀).subtype = (Z F₀ a).map (G₀).subtype ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = 2^m ∧
      Nat.card ((Q F₀ a).map (G₀).subtype) = (2^n)^2 ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) = (2^n)^2 * 2^m ∧
      Nat.card (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) =
        (2^n)^2 * (2^m)^2 := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨hnm,hQa,_,hZb,hZa,hQb,hE⟩ := reduced_linear_linear_profile h d hc hb hcomm
    n m hn hm (ha.of_mulEquiv eqa) (hbmodel.of_mulEquiv eqb)
  refine ⟨hnm,congrArg (map (G₀).subtype) hQa,?_⟩
  simpa only [card_map_of_injective (G₀).subtype_injective,hQa] using ⟨hZb,hZa,hQb,hE⟩

/-- The numerical clause (11.7)(c) for the two-core of the full original
Borel, not merely an abstract subgroup of the reduced graph. -/
theorem original_linear_linear_borel_core_order (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (ha : ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2 ^ n))
    (hbmodel : ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2 ^ m)) :
    n = 2*m ∧ Nat.card (twoCore (commonBorel L S)) = (2^n)^2 * (2^m)^2 := by
  obtain ⟨hnm,_,_,_,_,hE⟩ := original_reduced_linear_linear_profile h d hc hb hcomm n m hn hm ha hbmodel
  have ht := Reduction.reduced_triple h
  have hBG : Reduction.B₀ L S ≤ G₀ :=
    (show Reduction.B₀ L S ≤ Reduction.P₀ L S 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L S) ≤ G₀ :=
    (show twoCore (commonBorel L S) ≤ Reduction.B₀ L S from le_sup_right).trans hBG
  have hmap : (((stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2).map
      (G₀).subtype) = twoCore (commonBorel L S) := by
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (Reduction.B₀ L S).subgroupOf G₀ from ht.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  exact ⟨hnm,hmap ▸ hE⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
