module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryBetaCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaProfile
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.Frattini.Intersection

/-!
# Full centers and extraspecial structure in the original binary-beta branch

Thickness supplies the source turns, so the intrinsic PSL2(2^n)/SL2(2)
markings give Z(Q_beta) = Z(S_0) = Z_beta and make the literal first seed
self-centralizing in Q_beta without any extra geometric choices.

At the already marked field-four parameter, the proved center order two
identifies the nonzero derived subgroup with Z_beta. The Frattini identity
and elementary central quotient then make the actual beta core extraspecial
of order 32. Its original seed is a normal self-centralizing elementary
subgroup of order eight. Both full centers and the complete extraspecial,
derived and Frattini conclusions are transported through the original
reduced-group inclusion, with quotient markings on the literal images.

This discharges these central-series premises for the field-four/binary
profile. General field and row selection, the other Chapter 11 profiles
and unconditional marked recognition remain further source obligations;
the earlier local inputs are retained.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.3), (11.6)--(11.7), printed pp.168--175; reduced amalgam, pp.95--96.
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

private theorem linear_coordinates {H : Type*} [Group H] {n : ℕ}
    (hM : ClassicalGroup.IsPSL H 2 (2 ^ n)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      Nonempty (H ≃* SL(2,k)) := by
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := hM
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact ⟨k,hk,hfin,inferInstance,⟨e.trans f.symm⟩⟩

/-- Both full centers in the actual reduced graph, without selecting the alpha field. -/
theorem reduced_linear_binary_centers (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    centerIn (Q F₀ b) = Z F₀ b ∧
      centerIn ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = Z F₀ b := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := source_turns h hc hb
  obtain ⟨k,hk,hfin,hchar,⟨ea⟩⟩ := linear_coordinates ha
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  exact ⟨source_linear_binary_core_center ht hB d hc hb hcomm hbc hac
    (.linear n hn ha) ea eb g hga hgb,
    source_linear_binary_edge_center ht hB d hc hb hcomm hbc hac
    (.linear n hn ha) ea eb g hga hgb⟩

private theorem centerIn_map_injective {A H : Type*} [Group A] [Group H]
    (Q : Subgroup A) (f : A →* H) (hf : Function.Injective f) :
    (centerIn Q).map f = centerIn (Q.map f) := by
  rw [centerIn_eq_map_center,centerIn_eq_map_center,map_embeddedCenter Q f hf]

/-- Full centers after the original inclusion, with both quotient markings
on the actual original-group images. -/
theorem original_reduced_linear_binary_centers (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2 ^ n))
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SL(2,ZMod 2)) :
    centerIn ((Q F₀ b).map (G₀).subtype) = (Z F₀ b).map (G₀).subtype ∧
      centerIn (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) =
        (Z F₀ b).map (G₀).subtype := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  obtain ⟨hQ,hE⟩ := reduced_linear_binary_centers h d hc hb hcomm n hn
    (ha.of_mulEquiv eqa) (eqb.trans eb)
  exact ⟨(centerIn_map_injective _ _ (G₀).subtype_injective).symm.trans
    (congrArg (map (G₀).subtype) hQ),
    (centerIn_map_injective _ _ (G₀).subtype_injective).symm.trans
    (congrArg (map (G₀).subtype) hE)⟩

/-- In the field-four/binary branch the actual beta core is extraspecial
of order 32. Its derived, Frattini and full central layers all equal Z_beta. -/
theorem reduced_linear_four_binary_extraspecial (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    IsExtraspecial 2 (Q F₀ b) ∧ Nat.card (Q F₀ b) = 32 ∧
      (frattini (Q F₀ b)).map (Q F₀ b).subtype = Z F₀ b ∧
      ⁅Q F₀ b,Q F₀ b⁆ = Z F₀ b := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := source_turns h hc hb
  have hs := reduced_linear_binary_core_structure h d hc hb hcomm hbc hac
    2 (by decide) ha eb g hga hgb
  obtain ⟨_,_,hZ,hZa,hQ,hE⟩ := reduced_linear_four_binary_profile h d hc hb hcomm ha eb
  let : Finite (Q F₀ b) := Nat.finite_of_card_ne_zero (by omega)
  let : Finite (Z F₀ b) := Nat.finite_of_card_ne_zero (by omega)
  have hcenter := (reduced_linear_binary_centers h d hc hb hcomm 2 (by decide) ha eb).1
  have hderived : ⁅Q F₀ b,Q F₀ b⁆ = Z F₀ b := by
    have hd := card_dvd_of_le hs.2.2.2.2.2.2.1
    rw [hZ] at hd
    have hcD : Nat.card (⁅Q F₀ b,Q F₀ b⁆ : Subgroup G₀) = 2 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
      · exact (hs.2.2.2.2.2.1 (card_eq_one.mp h1)).elim
      · exact h2
    exact eq_of_le_of_card_ge hs.2.2.2.2.2.2.1 (by rw [hZ,hcD])
  have hfrattini : (frattini (Q F₀ b)).map (Q F₀ b).subtype = Z F₀ b :=
    hs.2.2.2.2.1.trans hderived
  have hzsub : (Z F₀ b).subgroupOf (Q F₀ b) = center (Q F₀ b) := by
    rw [←hcenter,centerIn_eq_map_center,subgroupOf,
      comap_map_eq_self_of_injective (Q F₀ b).subtype_injective]
  obtain ⟨hN,hquot,helem⟩ := reduced_linear_binary_core_quotient h d hc hb hcomm
    hbc hac 2 (by decide) ha eb g hga hgb
  have hcenterCard : Nat.card (center (Q F₀ b)) = 2 := by
    rw [←card_map_of_injective (Q F₀ b).subtype_injective,←centerIn_eq_map_center,hcenter,hZ]
  let := hN
  let e := QuotientGroup.quotientMulEquivOfEq hzsub
  let := helem
  let : Nontrivial ((Q F₀ b) ⧸ (Z F₀ b).subgroupOf (Q F₀ b)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hquot]; norm_num)
  refine ⟨⟨hcenterCard,IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective,
    e.symm.toEquiv.nontrivial⟩,hQ,hfrattini,hderived⟩

/-- The self-centralizer assertion concerns the actual first seed in the
original reduced beta core, for every linear alpha field. -/
theorem reduced_linear_binary_seed_centralizer (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    Q F₀ b ⊓ centralizer (Z F₀ a ⊓ Q F₀ b : Set G₀) = Z F₀ a ⊓ Q F₀ b := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := source_turns h hc hb
  obtain ⟨k,hk,hfin,hchar,⟨ea⟩⟩ := linear_coordinates ha
  exact source_linear_binary_seed_centralizer (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac
    (.linear n hn ha) ea eb g hga hgb

/-- The actual field-four seed is a normal self-centralizing elementary
eight inside the extraspecial beta core, retaining its original placement. -/
theorem reduced_linear_four_binary_seed (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    let E := Z F₀ a ⊓ Q F₀ b
    IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      (E.subgroupOf (Q F₀ b)).Normal ∧ Q F₀ b ⊓ centralizer (E : Set G₀) = E := by
  let ht := Reduction.reduced_triple h
  let E := Z F₀ a ⊓ Q F₀ b
  change IsElementaryAbelian 2 E ∧ _
  let : IsElementaryAbelian 2 (Z F₀ a) := source_center_elementary ht a
  have hEa : E ≤ Z F₀ a := inf_le_left
  have helem : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hEa
  have hidx := source_binary_seed_index ht d hc hb eb
  change E.relIndex (Z F₀ a) = 2 at hidx
  have hcZa := (reduced_linear_four_binary_profile h d hc hb hcomm ha eb).2.2.2.1
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G₀) E (Z F₀ a) bot_le hEa
  rw [relIndex_bot_left,relIndex_bot_left,hidx,hcZa] at hcount
  have hE : Nat.card E = 8 := by omega
  have hn : Q F₀ b ≤ normalizer (E : Set G₀) :=
    (le_inf (source_adjacent_core_normalizes_center ht (source_critical_one_adjacent hc hb))
      (Q F₀ b).le_normalizer).trans inf_normalizer_le_normalizer_inf
  exact ⟨helem,hE,normal_subgroupOf_of_le_normalizer hn,
    reduced_linear_binary_seed_centralizer h d hc hb hcomm 2 (by decide) ha eb⟩

/-- Extraspecial structure and its exact derived and Frattini layers survive
the original inclusion. No group-family label replaces these literal subgroups. -/
theorem original_reduced_linear_four_binary_extraspecial (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 4)
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SL(2,ZMod 2)) :
    let Qb := (Q F₀ b).map (G₀).subtype
    IsExtraspecial 2 Qb ∧ Nat.card Qb = 32 ∧
      (frattini Qb).map Qb.subtype = (Z F₀ b).map (G₀).subtype ∧
      ⁅Qb,Qb⁆ = (Z F₀ b).map (G₀).subtype := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  obtain ⟨hextra,hcard,hphi,hder⟩ := reduced_linear_four_binary_extraspecial h d hc hb hcomm
    (ha.of_mulEquiv eqa) (eqb.trans eb)
  refine ⟨IsExtraspecial.of_mulEquiv
    ((Q F₀ b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective) hextra,?_,?_,?_⟩
  · simpa only [card_map_of_injective (G₀).subtype_injective] using hcard
  · rw [frattini_image_map _ _ (G₀).subtype_injective,hphi]
  · rw [←map_commutator,hder]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
