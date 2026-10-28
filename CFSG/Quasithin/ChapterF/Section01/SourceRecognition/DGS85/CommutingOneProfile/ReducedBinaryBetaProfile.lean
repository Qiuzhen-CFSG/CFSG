module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FiveEdgeFixers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathExistence
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The field-four/binary profile from intrinsic reduced markings

The binary beta Sylow normalizer is the Sylow itself. Its literal preimage
is therefore the edge two-core. The defining reduced Borel product makes
the alpha local actor the full alpha stabilizer. The same beta quotient
has three neighbors by orbit-stabilizer, keeping the full local kernel
separate from the two-core.

For an intrinsic PSL2(4) alpha marking these two facts discharge the full
A5 marking and cubic-valence premises of the existing center-order and
five-edge-fixer theorems. The actual core orders are 16 and 32, the edge
two-core has order 64, and five-edge nonbacktracking fixers have odd order.
This does not select the fields or finish all Chapter 11 branches.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6)--(11.7), pp.172--175; local reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem binary_rankOne {H : Type*} [Group H] (e : H ≃* SL(2,ZMod 2)) :
    IsRankOneModel H := by
  let f : SL(2,ZMod 2) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (ZMod 2))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact .linear 1 (by decide) ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e.trans f⟩⟩

/-- The binary local Borel is precisely the full edge two-core.
The full vertex stabilizer is not identified with the local actor. -/
theorem source_binary_local_edge_eq_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    d.localGroup b ⊓ stabilizer (family P) a =
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 := by
  let := finite_endpoints h
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  let q := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := eb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  let R := T.mapSurjective hq
  have hcard : Nat.card R = 2 := by
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive (ZMod 2) 2 R).symm.toEquiv).trans
      (by simp)
  have hnR : normalizer (R : Set (SL(2,ZMod 2))) = (R : Subgroup (SL(2,ZMod 2))) := by
    apply (eq_of_le_of_card_ge (R : Subgroup (SL(2,ZMod 2))).le_normalizer ?_).symm
    rw [Matrix.SpecialLinearGroup.card_sylow_normalizer_even,hcard]
    simp
  have hnT : normalizer (T : Set L) = (T : Subgroup L) := by
    have hm := T.normalizer_map_surjective q hq
    change (normalizer (T : Set L)).map q = normalizer (R : Set (SL(2,ZMod 2))) at hm
    rw [hnR] at hm
    have he := congrArg (comap q) hm
    change ((normalizer (T : Set L)).map q).comap q = ((T : Subgroup L).map q).comap q at he
    rw [comap_map_eq,comap_map_eq,
      sup_eq_left.mpr ((hk ▸ pCore_isPGroup.le_sylow_of_normal T).trans (T : Subgroup L).le_normalizer),
      sup_eq_left.mpr (hk ▸ pCore_isPGroup.le_sylow_of_normal T)] at he
    exact he
  have he := (source_edge_local_normalizer h d hab.symm (binary_rankOne eb) T hT).2
  rw [hnT] at he
  have hm := congrArg (map L.subtype) he
  rw [subgroupOf_map_subtype,hT] at hm
  simpa only [inf_comm] using hm

/-- The intrinsic binary beta quotient gives exactly three actual neighbors. -/
theorem source_binary_neighbor_card (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    Nat.card ((graph (family P)).neighborSet b) = 3 := by
  let := finite_endpoints h
  let D := d.localGroup b
  let : Finite D := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  let q := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := eb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  let R := T.mapSurjective hq
  have hRT : (R : Subgroup SL(2,ZMod 2)).comap q = T := by
    change ((T : Subgroup D).map q).comap q = _
    rw [comap_map_eq,hk,sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)]
  have hN : (normalizer (R : Set SL(2,ZMod 2))).comap q = normalizer (T : Set D) := by
    change (normalizer ((R : Subgroup SL(2,ZMod 2)) : Set SL(2,ZMod 2))).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,hRT]
    rfl
  have hidx : (normalizer (T : Set D)).index = 3 := by
    rw [←hN,index_comap_of_surjective _ hq]
    have hn : Nat.card (normalizer (R : Set SL(2,ZMod 2))) = 2 := by
      change Nat.card (normalizer ((R : Subgroup SL(2,ZMod 2)) : Set SL(2,ZMod 2))) = 2
      rw [Matrix.SpecialLinearGroup.card_sylow_normalizer_even]
      simp
    have hd : Nat.card SL(2,ZMod 2) = 6 := by
      simpa using (BenderSuzuki.External.huppert614_card_specialLinearGroup (K := ZMod 2))
    have hi := (normalizer (R : Set SL(2,ZMod 2))).card_mul_index
    rw [hn,hd] at hi
    omega
  have he := (source_edge_local_normalizer h d hab.symm (binary_rankOne eb) T hT).2
  have hstab : MulAction.stabilizer D a = normalizer (T : Set D) := he
  have horbit : MulAction.orbit D a = (graph (family P)).neighborSet b := by
    ext v
    constructor
    · rintro ⟨t,rfl⟩
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) (t : G)).map_adj_iff.mpr hab.symm
      change (graph (family P)).Adj ((t : G) • b) ((t : G) • a) at hh
      rwa [show (t : G) • b = b from d.local_le b t.property] at hh
    · intro hv
      obtain ⟨t,ht,hta⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hv⟩
      exact ⟨⟨t,ht⟩,hta⟩
  rw [←horbit,Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D a),
    ←index_eq_card,hstab,hidx]

private theorem graphLocalGroup_le_data (d : EarlierLocalTheorems (family P))
    (v : Vertex (family P)) : graphLocalGroup (family P) v ≤ d.localGroup v := by
  change sylowGenerated (stabilizer (family P) v) ≤ _
  exact iSup_le (d.sylow_le v)

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

private theorem reduced_base_local_eq_full (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀) (i : Bool)
    (eb : (d.localGroup (base F₀ (!i)) ⧸ pCore 2 (d.localGroup (base F₀ (!i)))) ≃* SL(2,ZMod 2)) :
    d.localGroup (base F₀ i) = stabilizer F₀ (base F₀ i) := by
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  let f := (G₀).subtype
  let a := base F₀ i
  let b := base F₀ (!i)
  have hA : family (Reduction.enlargedEndpoint L S) i ≤ (d.localGroup a).map f := by
    have hm : (graphLocalGroup F₀ a).map (G₀).subtype ≤ (d.localGroup a).map f :=
      map_mono (graphLocalGroup_le_data d a)
    exact (Reduction.reduced_graphLocalGroup_image h i).symm.le.trans hm
  have hD : family (Reduction.enlargedEndpoint L S) (!i) ≤ (d.localGroup b).map f := by
    have hm : (graphLocalGroup F₀ b).map (G₀).subtype ≤ (d.localGroup b).map f :=
      map_mono (graphLocalGroup_le_data d b)
    exact (Reduction.reduced_graphLocalGroup_image h (!i)).symm.le.trans hm
  have hAg : family (starredParabolic L S) i ⊔ (commonBorel L S).pCoreIn 2 ≤ (d.localGroup a).map f := by
    cases i <;> exact hA
  have hDg : family (starredParabolic L S) (!i) ≤ (d.localGroup b).map f := by
    apply le_trans _ hD
    cases i <;> exact le_sup_left
  have ha : (stabilizer F₀ a).map f = family (Reduction.P₀ L S) i := by
    have hs : stabilizer F₀ a = (family (Reduction.P₀ L S) i).subgroupOf G₀ := by
      change MulAction.stabilizer (G₀) (Subgroup.CosetGeometry.base F₀ i) = _
      rw [Subgroup.CosetGeometry.stabilizer_base]
      cases i <;> rfl
    rw [hs]
    apply map_subgroupOf_eq_of_le
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hab : (graph F₀).Adj a b :=
    ⟨by cases i <;> exact Bool.noConfusion,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hedge : d.localGroup b ⊓ stabilizer F₀ a ≤ d.localGroup a := by
    have he : d.localGroup b ⊓ stabilizer F₀ a = (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 :=
      source_binary_local_edge_eq_core ht hB d hab eb
    obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht hB d hab
    exact he.le.trans (hT ▸ map_subtype_le _)
  have hmapEdge : (d.localGroup b).map f ⊓ family (Reduction.P₀ L S) i ≤ (d.localGroup a).map f := by
    rw [←ha,←map_inf _ _ _ (G₀).subtype_injective]
    exact map_mono hedge
  have hred : Reduction.B₀ L S = (commonBorel L S ⊓ family (starredParabolic L S) i) ⊔
      (commonBorel L S ⊓ family (starredParabolic L S) (!i)) ⊔ (commonBorel L S).pCoreIn 2 := by
    cases i
    · rfl
    · change _ ⊔ _ ⊔ _ = _ ⊔ _ ⊔ _
      rw [sup_comm (commonBorel L S ⊓ starredParabolic L S 0)
        (commonBorel L S ⊓ starredParabolic L S 1)]
      rfl
  have hP : family (Reduction.P₀ L S) i = family (starredParabolic L S) i ⊔ Reduction.B₀ L S := by
    cases i <;> rfl
  have hB0 : Reduction.B₀ L S ≤ (d.localGroup a).map f := by
    rw [hred]
    apply sup_le (sup_le ?_ ?_) ?_
    · exact inf_le_right.trans (le_sup_left.trans hAg)
    · apply (le_inf (inf_le_right.trans hDg) ?_).trans hmapEdge
      rw [hP,hred]
      exact le_sup_right.trans (le_sup_left.trans le_sup_right)
    · exact le_sup_right.trans hAg
  apply le_antisymm (d.local_le (base F₀ i))
  apply (map_le_map_iff_of_injective (f := f) (G₀).subtype_injective).mp
  change (stabilizer F₀ a).map f ≤ (d.localGroup a).map f
  rw [ha,hP]
  exact sup_le (le_sup_left.trans hAg) hB0

/-- At every actual reduced edge, a binary beta local quotient makes
alpha's local actor the full alpha stabilizer. This uses the defining
reduced-Borel product and both original starred endpoints. -/
theorem reduced_binary_alpha_local_eq_full (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hab : (graph F₀).Adj a b)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    d.localGroup a = stabilizer F₀ a := by
  obtain ⟨g,ha,hb⟩ := incident_common_translate F₀ hab.2
  have ht : b.type = !a.type := Bool.eq_not_of_ne hab.1.symm
  rw [ht] at hb
  let v := base F₀ (!a.type)
  have hv : g • v = b := hb
  let eL := ((d.localGroup v).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr ((d.conjugate g v).symm.trans (congrArg d.localGroup hv)))
  let e₀ := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans eb
  have he := reduced_base_local_eq_full h d a.type e₀
  rw [←ha,d.conjugate,stabilizer_translate,he]

private def reduced_four_alpha_marking (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hab : (graph F₀).Adj a b)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    (stabilizer F₀ a ⧸ pCore 2 (stabilizer F₀ a)) ≃* alternatingGroup (Fin 5) := by
  apply Classical.choice
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := ha
  obtain ⟨ek⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
  let eL := MulEquiv.subgroupCongr (reduced_binary_alpha_local_eq_full h d hab eb).symm
  exact ⟨((QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans e).trans ek⟩

/-- The actual field-four/binary core and order profile. Full alpha marking,
center order and choices of turns are all discharged from the reduced source. -/
theorem reduced_linear_four_binary_profile (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    Q F₀ a = Z F₀ a ∧ betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      Nat.card (Z F₀ b) = 2 ∧ Nat.card (Z F₀ a) = 16 ∧
      Nat.card (Q F₀ b) = 32 ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = 64 := by
  let ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hab := source_critical_one_adjacent hc hb
  have hval (v : Vertex F₀) : 3 ≤ Nat.card ((graph F₀).neighborSet v) := by
    rw [card_neighbors_of_indices F₀ (fun i => ((F₀ (!i)).subgroupOf (F₀ i)).index) (fun _ => rfl)]
    exact source_valence_ge_three ht hS v.type
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F₀).neighborSet b)
    (by rw [←Nat.card_coe_set_eq]; have hh := hval b; omega) a
  obtain ⟨b',hab',hb'b⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F₀).neighborSet a)
    (by rw [←Nat.card_coe_set_eq]; have hh := hval a; omega) b
  obtain ⟨g,hga,hgb'⟩ := locally_transitive F₀ hab hab'
  have hgb : g • b ≠ b := by rw [hgb']; exact hb'b
  let ef := reduced_four_alpha_marking h d hab ha eb
  have hthree := source_binary_neighbor_card ht hB d hab eb
  have hZb := source_cubic_a5_center_card_two ht hB hS hc hb hcomm hbc hca.symm hthree ef g hga hgb
  change Nat.card (Z F₀ b) = 2 at hZb
  have hs := reduced_linear_binary_core_structure h d hc hb hcomm hbc hca.symm
    2 (by decide) ha eb g hga hgb
  have ho := reduced_linear_binary_local_orders h d hc hb hcomm hbc hca.symm
    2 (by decide) ha eb g hga hgb
  refine ⟨hs.2.1,hs.2.2.2.1,hZb,?_,?_,?_⟩
  · rw [ho.2.2.1,hZb]
    norm_num
  · rw [ho.2.2.2.1,hZb]
    norm_num
  · rw [ho.2.2.2.2,hZb]
    norm_num

/-- Odd order of the literal five-edge fixer, with only intrinsic quotient
markings. Closed source paths are allowed; only backtracking is excluded. -/
theorem reduced_linear_four_binary_five_edge_fixer_odd (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {v₀ v₁ a b c v₅ : Vertex F₀}
    (h01 : (graph F₀).Adj v₀ v₁) (h1a : (graph F₀).Adj v₁ a)
    (hc : IsCriticalPair F₀ a b) (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hc5 : (graph F₀).Adj c v₅)
    (h0a : v₀ ≠ a) (h1b : v₁ ≠ b) (hac : a ≠ c) (hb5 : b ≠ v₅)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) :
    Odd (Nat.card (stabilizer F₀ v₀ ⊓ stabilizer F₀ v₁ ⊓ stabilizer F₀ a ⊓
      stabilizer F₀ b ⊓ stabilizer F₀ c ⊓ stabilizer F₀ v₅ : Subgroup G₀)) := by
  have hab := source_critical_one_adjacent hc hb
  exact source_cubic_a5_five_edge_fixer_odd (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    h01 h1a hc hb hcomm hbc hc5 h0a h1b hac hb5
    (source_binary_neighbor_card (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h) d hab eb)
    (reduced_four_alpha_marking h d hab ha eb)
/-- The same field-four/binary orders on the literal subgroups of the
original completion. Both input quotient markings are on their original images. -/
theorem original_reduced_linear_four_binary_orders (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 4)
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* SL(2,ZMod 2)) :
    Nat.card ((Z F₀ b).map (G₀).subtype) = 2 ∧
      Nat.card ((Q F₀ a).map (G₀).subtype) = 16 ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) = 32 ∧
      Nat.card (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) = 64 := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  obtain ⟨hQa,_,hZb,hZa,hQb,hE⟩ := reduced_linear_four_binary_profile h d hc hb hcomm
    (ha.of_mulEquiv eqa) (eqb.trans eb)
  simpa only [card_map_of_injective (G₀).subtype_injective,hQa] using ⟨hZb,hZa,hQb,hE⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
