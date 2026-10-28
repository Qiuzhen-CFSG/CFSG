module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Rank-one containing cases for moved local-component maximality

Retain the original full Sylow subgroup when passing to the containing
component and to its two-core quotient. Binary rank-one proper Sylow
overgroups are solvable, so they admit no proper local C-component.
For an odd-prime PSL₂ containing quotient, Dickson's theorem forces the
smaller image to be A₅. The two-core quotient equivalence translates
this to precisely PSL₂(4) on the original smaller subgroup.

Equality of the images lifts to equality of the actual components:
the quotient kernel lies in the full Sylow, so the larger component
already lies in the smaller component's local join, where minimality
applies. The source four-model theorem then leaves only a Sylow-invariant
overcomponent or the J₁ containing quotient. Excluding those remaining
cases is still necessary for the unrestricted maximality theorem.

Source: Aschbacher--Smith, A.3.12, printed pp.47--48, and
1.2.8(1--3), printed pp.506--507 of the combined manuscript.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Equality in the literal ambient two-core quotient lifts using the retained full Sylow. -/
theorem eq_of_twoCore_images_eq (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (he : B.map (QuotientGroup.mk' (pCore 2 G)) =
      K.map (QuotientGroup.mk' (pCore 2 G))) : B = K := by
  have hKM : K ≤ B ⊔ (T : Subgroup G) := by
    have hh := le_comap_map (QuotientGroup.mk' (pCore 2 G)) K
    rw [←he, comap_map_eq, QuotientGroup.ker_mk'] at hh
    exact hh.trans (sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal T) B)
  have he' := hB.eq_of_le (hK.subgroupOf hKM) (comap_mono hBK)
  simpa only [map_subgroupOf_eq_of_le (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left),
    map_subgroupOf_eq_of_le hKM] using congrArg (map (B ⊔ (T : Subgroup G)).subtype) he'

/-- A Bender containing quotient admits no proper local C-component. -/
theorem eq_of_bender_quotient (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K)) : B = K := by
  apply eq_of_solvable_sylow_overgroups T hB hK hBK
  exact isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    (bender_solvable_proper_sylow_overgroup hm)

private theorem psl_four_of_alternating_five {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : ClassicalGroup.IsPSL X 2 4 := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hc, ⟨e.trans f.symm⟩⟩

private theorem psl_four_quotient_of_image {B : Subgroup G}
    (hm : LocalModels.IsAlternating (B.map (QuotientGroup.mk' (pCore 2 G))) 5) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := B.map q
  obtain ⟨e⟩ := hm
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup D := e.isSimpleGroup
  have hc : pCore 2 D = ⊥ := by
    apply (inferInstance : (pCore 2 D).Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    have hn : Group.IsSolvable D := by
      let : Group.IsNilpotent (pCore 2 D) := pCore_isNilpotent
      let : Group.IsSolvable (⊤ : Subgroup D) := ht ▸
        (inferInstance : Group.IsSolvable (pCore 2 D))
      exact Group.isSolvable_of_surjective (f := (topEquiv (G := D)).toMonoidHom)
        (topEquiv (G := D)).surjective
    let := hn
    have hs : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) hs
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap B)
    (q.subgroupMap_surjective B) hk
  let b : (D ⧸ pCore 2 D) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact psl_four_of_alternating_five (a.trans (b.trans e))

/-- In an odd-prime PSL₂ containing quotient, a non-PSL₂(4) local component is the whole component. -/
theorem eq_of_primePSL2_quotient (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) : B = K := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let := pCore_isNilpotent (p := 2) (G := G)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hb : B.map q ∈ localCComponents S := by
    simpa only [S, Sylow.coe_mapSurjective] using localCComponents_map_of_solvable_ker hB q
  by_cases he : B.map q = K.map q
  · exact eq_of_twoCore_images_eq T hB hK hBK he
  · exact (hnot (psl_four_quotient_of_image
      (proper_primePSL2_models S hb (hK.map_quotient _) (map_mono hBK) he hp ho
        (hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm)).2)).elim

omit [Finite G] in
private theorem quotient_subgroupOf_equiv {K H : Subgroup G} (hKH : K ≤ H) :
    Nonempty (((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) ≃* (K ⧸ pCore 2 K)) :=
  ⟨QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))⟩

/-- The rank-one exclusions for the actual Chapter 1 local chain, before quotienting. -/
theorem local_chain_eq_of_rankOne_quotient (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G)) (hBK : B ≤ K)
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) : B = K := by
  let H := K ⊔ (T : Subgroup G)
  have hBH : B ≤ H := hBK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hb : B.subgroupOf H ∈ localCComponents S :=
    ((mem_LIn_iff_subgroupOf le_sup_right hBH).mp ⟨hBH,hB⟩).1
  let eK := (quotient_subgroupOf_equiv (show K ≤ H from le_sup_left)).some
  have he : B.subgroupOf H = K.subgroupOf H := by
    rcases hm with hm | ⟨p,hp,ho,hm⟩
    · exact eq_of_bender_quotient S hb hK.1 (comap_mono hBK) (hm.of_mulEquiv eK)
    · apply eq_of_primePSL2_quotient S hb hK.1 (comap_mono hBK) _ hp ho (hm.of_mulEquiv eK)
      intro hh
      exact hnot (hh.of_mulEquiv (quotient_subgroupOf_equiv hBH).some.symm)
  simpa only [map_subgroupOf_eq_of_le hBH,
    map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] using congrArg (map H.subtype) he

/-- A strict overcomponent of a non-PSL₂(4) local component is Sylow-invariant or has quotient J₁. -/
theorem local_chain_eq_or_normalized_or_janko
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G)) (hBK : B ≤ K)
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) :
    B = K ∨ (T : Subgroup G) ≤ normalizer (K : Set G) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  let H := K ⊔ (T : Subgroup G)
  have hQ := uniqueness_local_quotient_sqtk hG hK.2.2
  rcases proposition_1_2_1_three_index_knownSimple hQ hK.1 with hn | ⟨_,hm⟩
  · exact Or.inr (Or.inl (le_sup_right.trans
      ((normal_subgroupOf_iff_le_normalizer (show K ≤ H from le_sup_left)).mp hn)))
  · have hmK := hm.of_mulEquiv (quotient_subgroupOf_equiv (show K ≤ H from le_sup_left)).some.symm
    cases hmK with
    | linear_even n hn hmodel =>
      exact Or.inl (local_chain_eq_of_rankOne_quotient T hB hK hBK hnot
        (Or.inl (.linear n hn hmodel)))
    | suzuki m hm hmodel =>
      exact Or.inl (local_chain_eq_of_rankOne_quotient T hB hK hBK hnot
        (Or.inl (.suzuki m hm hmodel)))
    | linear_prime p hp ho hmodel =>
      exact Or.inl (local_chain_eq_of_rankOne_quotient T hB hK hBK hnot
        (Or.inr ⟨p,hp,ho,hmodel⟩))
    | janko hmodel => exact Or.inr (Or.inr hmodel)

/-- Movement in the original Sylow orbit gives the four actual quotient models of 1.2.1(3). -/
theorem moved_local_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    NonnormalCComponentModel (B ⧸ pCore 2 B) := by
  rcases proposition_1_2_1_three_index_knownSimple
    (uniqueness_local_quotient_sqtk hG hB.2.2) hB.1 with hn | ⟨_,hmodel⟩
  · have hT : (T : Subgroup G) ≤ normalizer (B : Set G) :=
      le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
        (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).mp hn)
    exact (hm.not_ge (conjugateSpanBy_le le_rfl hT)).elim
  · exact hmodel.of_mulEquiv (quotient_subgroupOf_equiv
      (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).some.symm

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
