module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.DihedralCenterOrder
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Excluding the actual reduced field-four/dihedral branch

The D10 Sylow normalizer has order two, so its preimage in the beta local
actor is exactly the full edge two-core. In the defining reduced-Borel
product, the beta starred intersection is therefore absorbed by the alpha
local actor. The alpha starred intersection and original Borel two-core
are already there. Thus the alpha local actor is the full alpha stabilizer.
Both base orientations and every translated edge are covered.

A genuine intrinsic PSL2(4) marking consequently supplies the full A5
marking needed by the center-order proof and the dihedral exclusion.
No center order, core identity, full-alpha marking, or chosen turn remains
as an extra premise. The final application keeps both quotient markings
on their actual images under the reduced-to-original inclusion.
The earlier local inputs remain explicit. General alpha row selection,
other field sizes, and the remaining Chapter 11 profiles are separate.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
reduction, printed pp.95--96; (11.6)--(11.7), printed pp.172--175.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The dihedral local Borel is precisely the full edge two-core.
The full vertex stabilizer is not identified with the local actor. -/
theorem source_dihedral_local_edge_eq_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
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
    rw [R.card_eq_multiplicity,DihedralGroup.nat_card]
    decide +kernel
  have hnR : normalizer (R : Set (DihedralGroup 5)) = (R : Subgroup (DihedralGroup 5)) :=
    odd_dihedral_two_subgroup_normalizer 5 (by decide) (MulEquiv.refl _) R R.isPGroup'
      (fun he => by simp [he] at hcard)
  have hnT : normalizer (T : Set L) = (T : Subgroup L) := by
    have hm := T.normalizer_map_surjective q hq
    change (normalizer (T : Set L)).map q = normalizer (R : Set (DihedralGroup 5)) at hm
    rw [hnR] at hm
    have he := congrArg (comap q) hm
    change ((normalizer (T : Set L)).map q).comap q = ((T : Subgroup L).map q).comap q at he
    rw [comap_map_eq,comap_map_eq,
      sup_eq_left.mpr ((hk ▸ pCore_isPGroup.le_sylow_of_normal T).trans (T : Subgroup L).le_normalizer),
      sup_eq_left.mpr (hk ▸ pCore_isPGroup.le_sylow_of_normal T)] at he
    exact he
  have he := (source_edge_local_normalizer h d hab.symm (.dihedral ⟨eb⟩) T hT).2
  rw [hnT] at he
  have hm := congrArg (map L.subtype) he
  rw [subgroupOf_map_subtype,hT] at hm
  simpa only [inf_comm] using hm

private theorem graphLocalGroup_le_data (d : EarlierLocalTheorems (family P))
    (v : Vertex (family P)) : graphLocalGroup (family P) v ≤ d.localGroup v := by
  change sylowGenerated (stabilizer (family P) v) ≤ _
  exact iSup_le (d.sylow_le v)

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

private theorem reduced_base_local_eq_full (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀) (i : Bool)
    (eb : (d.localGroup (base F₀ (!i)) ⧸ pCore 2 (d.localGroup (base F₀ (!i)))) ≃* DihedralGroup 5) :
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
      source_dihedral_local_edge_eq_core ht hB d hab eb
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

/-- At every actual reduced edge, a dihedral beta local quotient makes
alpha's local actor the full alpha stabilizer. This uses the defining
reduced-Borel product and both original starred endpoints. -/
theorem reduced_dihedral_alpha_local_eq_full (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hab : (graph F₀).Adj a b)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
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

/-- The actual reduced field-four/dihedral candidate is excluded without
a full-alpha marking, core identity, center order or path-turn premise. -/
theorem reduced_linear_four_dihedral_exclusion (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) : False := by
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := ha
  obtain ⟨ek⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
  let eL := MulEquiv.subgroupCongr
    (reduced_dihedral_alpha_local_eq_full h d (source_critical_one_adjacent hc hb) eb).symm
  let ef := ((QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans e).trans ek
  exact source_a5_dihedral_exclusion (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    d hc hb hcomm ef eb

/-- The same exclusion with both quotient markings on the literal images
in the original completion. -/
theorem original_reduced_linear_four_dihedral_exclusion (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 4)
    (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* DihedralGroup 5) : False := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  exact reduced_linear_four_dihedral_exclusion h d hc hb hcomm (ha.of_mulEquiv eqa) (eqb.trans eb)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
