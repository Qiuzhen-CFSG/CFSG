module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityObstruction
public import Theory.GroupTheory.CComponent.RadicalPairOrder
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension
/-!
# The actual moved pair in a containing component

The original Sylow mover supplies distinct isomorphic C-components inside
its local join intersected with a normalized containing component. Their
simple radical quotient orders have a square dividing the containing radical
quotient order. The original moved component has radical equal to its two-core,
so the square constraint retains exactly the quotient in 1.2.8.

Source: Aschbacher--Smith, A.3.12 and 1.2.8, printed pp.47--48 and 506--507.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

private theorem component_image_ne {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    {A D : Subgroup X} (hA : A.IsCComponent) (hD : D.IsCComponent) (hne : A ≠ D) :
    A.map f ≠ D.map f := by
  intro he
  apply hne
  apply hA.eq_of_map_quotient_eq hD f.ker
  apply map_injective (f := (QuotientGroup.quotientKerEquivOfSurjective f hf).toMonoidHom)
    (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
  have hc : (QuotientGroup.quotientKerEquivOfSurjective f hf).toMonoidHom.comp
      (QuotientGroup.mk' f.ker) = f := by ext x; rfl
  simpa only [map_map, hc] using he

private theorem radical_card_image {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) [Group.IsSolvable f.ker] (A : Subgroup X) :
    Nat.card ((A.map f) ⧸ solvableRadical (A.map f)) =
      Nat.card (A ⧸ solvableRadical A) := by
  let g := f.subgroupMap A
  let : Group.IsSolvable g.ker := by
    rw [show g = f.subgroupMap A from rfl, ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := A.subtype.subgroupComap f.ker)
      (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : X)) he)))
  exact (Nat.card_congr (solvableRadicalQuotientEquiv g
    (f.subgroupMap_surjective A)).toEquiv).symm

/-- The original nonnormal component has simple intrinsic two-core quotient. -/
theorem moved_local_simple_core_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    IsSimpleGroup (B ⧸ pCore 2 B) := by
  let H := B ⊔ (T : Subgroup G)
  let A := B.subgroupOf H
  have hn : ¬ A.Normal := by
    intro hnormal
    have hT : (T : Subgroup G) ≤ normalizer (B : Set G) :=
      le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
        (show B ≤ H from le_sup_left)).mp hnormal)
    exact hm.not_ge (conjugateSpanBy_le le_rfl hT)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hQ := uniqueness_local_quotient_sqtk hG hB.2.2
  let Q := H ⧸ pCore 2 H
  let D := A.map (QuotientGroup.mk' (pCore 2 H))
  have hD : IsComponent Q D := nonnormal_twoCore_image_isComponent hQ hB.1 hn
  have hnD : ¬ D.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hB.1 _ hh)
  let : IsQuasisimple D := hD.2
  have hf : fittingSubgroup D ≤ center D :=
    (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hmodel := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hQ D hD.isCComponent hf).2
  let := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.simple_of_model
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
    (pCore_quotient_pCore_eq_bot 2) D hD hnD hmodel
  let a : (A ⧸ pCore 2 A) ≃* D := cComponentTwoCoreQuotientEquiv hB.1
  let b : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show B ≤ H from le_sup_left))
      (pCore_map_iso 2 (subgroupOfEquivOfLe (show B ≤ H from le_sup_left)))
  exact (b.symm.trans a).isSimpleGroup

/-- Thus the radical of the original moved component is its two-core. -/
theorem moved_local_radical_eq_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    solvableRadical B = pCore 2 B := by
  let := moved_local_simple_core_quotient hG T hB hm
  let := hB.1.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).surjective
  exact radical_eq_core_of_perfect_simple_core_quotient

/-- The original moving element gives two isomorphic simple radical quotients
whose squared order divides the containing radical quotient order. -/
theorem actual_pair_square_dvd
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T)
    (hBK : B ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    Nat.card (B ⧸ solvableRadical B) ^ 2 ∣ Nat.card (K ⧸ solvableRadical K) := by
  let J := B ⊔ (T : Subgroup G)
  let P := J ⊓ K
  have hBP : B ≤ P := le_inf le_sup_left hBK
  have hPK : P ≤ K := inf_le_right
  let A := B.subgroupOf P
  have hA : A.IsCComponent := hB.subgroupOf_of_le hBP inf_le_left
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (le_inf ((show (T : Subgroup G) ≤ J from le_sup_right).trans J.le_normalizer)
      hTK).trans inf_normalizer_le_normalizer_inf
  have hnon : ¬ (T : Subgroup G) ≤ normalizer (B : Set G) :=
    fun hn => hm.not_ge (conjugateSpanBy_le le_rfl hn)
  obtain ⟨t,ht,htB⟩ := Set.not_subset.mp hnon
  let e := P.normalizerMonoidHom ⟨t,hTP ht⟩
  let D := A.map e.toMonoidHom
  have hD : D.IsCComponent := hA.map_equiv e
  have hne : A ≠ D := by
    intro he
    apply htB
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hmaps : D.map P.subtype = B.map (MulAut.conj t).toMonoidHom := by
      change (A.map e.toMonoidHom).map P.subtype = _
      rw [map_map]
      have hc : P.subtype.comp e.toMonoidHom = (MulAut.conj t).toMonoidHom.comp P.subtype := rfl
      rw [hc, ← map_map, map_subgroupOf_eq_of_le hBP]
    change B.map (MulAut.conj t).toMonoidHom = B
    rw [← hmaps, ← he, map_subgroupOf_eq_of_le hBP]
  let q := QuotientGroup.mk' (solvableRadical K)
  let f := q.comp (inclusion hPK)
  let Y := f.range
  let g := f.rangeRestrict
  let : Group.IsSolvable f.ker := by
    rw [show f = q.comp (inclusion hPK) from rfl, ← MonoidHom.comap_ker]
    rw [show q = QuotientGroup.mk' (solvableRadical K) from rfl, QuotientGroup.ker_mk']
    exact Group.isSolvable_of_isSolvable_injective
      (f := (inclusion hPK).subgroupComap (solvableRadical K))
      (fun a b he => Subtype.ext (inclusion_injective hPK (congrArg Subtype.val he)))
  let : Group.IsSolvable g.ker := by
    have he : g.ker = f.ker := f.ker_rangeRestrict
    rw [he]
    infer_instance
  have hd := (cComponent_map_of_solvable_ker hA g f.rangeRestrict_surjective).radical_quotient_card_mul_dvd
    (cComponent_map_of_solvable_ker hD g f.rangeRestrict_surjective)
    (component_image_ne g f.rangeRestrict_surjective hA hD hne)
  rw [radical_card_image g A, radical_card_image g D] at hd
  let a : A ≃* B := subgroupOfEquivOfLe hBP
  let d : A ≃* D := e.subgroupMap A
  have ha := Nat.card_congr (QuotientGroup.congr _ _ a (map_solvableRadical_equiv a)).toEquiv
  have he := Nat.card_congr (QuotientGroup.congr _ _ d (map_solvableRadical_equiv d)).toEquiv
  rw [← he, ha, ← pow_two] at hd
  exact hd.trans Y.card_subgroup_dvd_card

/-- The square constraint uses the exact two-core quotient in 1.2.8. -/
theorem actual_pair_twoCore_square_dvd
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hBK : B ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    Nat.card (B ⧸ pCore 2 B) ^ 2 ∣ Nat.card (K ⧸ solvableRadical K) := by
  have hd := actual_pair_square_dvd T hB.1 hBK hTK hm
  rwa [moved_local_radical_eq_core hG T hB hm] at hd

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
