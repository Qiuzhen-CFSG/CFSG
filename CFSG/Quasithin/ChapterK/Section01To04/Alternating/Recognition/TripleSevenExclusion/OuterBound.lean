module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion.AssemblyInputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.Degree
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.NormalizerGeometry
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.NormalThreeSmallActor
public import Theory.Frattini.OmegaProducts

/-!
# Restricting small actors to the genuine triple cover of A7

Every elementary actor of ratio at most two lies in the triple-seven component.
Its faithful irreducible module has degree at least twelve, and ambient
elementary subgroups have rank at most three. The fixed-point-free cubic
center therefore cannot be inverted by a small actor. The proved normalizer
geometry places each center-fixing involution in the component.

The actual small cubic actor now restricts to the component and transports
through its specified isomorphism, preserving rank, fixed codimension and
cubicity. This proves the outer-extension restriction obligation without
assuming the intrinsic representation exclusion.

Source: Aschbacher--Smith K.1, printed p.452, invoking Guralnick--Malle,
*Classification of 2F-modules I*, Theorem 6.2 and Table 6.3.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}

/-- Every small elementary actor in the ambient group lies in its triple-seven component. -/
theorem tripleSeven_small_actor_le (h : Input ρ K L) (e : L ≃* TripleSeven)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) : A ≤ L := by
  let ι : TripleSeven →* G := L.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hrange : ι.range = L := by
    rw [MonoidHom.range_comp, e.symm.toMonoidHom.range_eq_top_of_surjective e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hn : ι.range.Normal := by rw [hrange, h.fitting]; infer_instance
  have hi : IsIrreducible (ρ.comp ι) :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hd := finrank_ge_twelve (ρ.comp ι) (h.faithful.comp hι) hi
  have hr : rank A ≤ 3 := by
    have hc := elementary_card_le_eight ι hι hn ρ h.faithful hi A hA.2
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [rank, show Nat.log 2 8 = 3 from by decide] using hh
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center TripleSeven) 3
    (by rw [tripleSeven_center_card])
  have hz3 : orderOf (z : TripleSeven) = 3 := (Subgroup.orderOf_coe z).trans hz
  have hz1 : (z : TripleSeven) ≠ 1 := by intro he; simp [he] at hz3
  have hgen : zpowers (z : TripleSeven) = center TripleSeven :=
    (cyclicThree_generator _ tripleSeven_center_card z z.property hz1).1
  have hcgen : zpowers (ι z) = (center TripleSeven).map ι := by
    rw [← MonoidHom.map_zpowers, hgen]
  have hcn : (zpowers (ι z)).Normal := by
    rw [hcgen]
    let := hn
    have he : (center TripleSeven).map ι = (center ι.range).map ι.range.subtype := by
      rw [← center_map_equiv (MonoidHom.ofInjective hι), map_map]
      rfl
    rw [he]
    exact ConjAct.normal_of_characteristic_of_normal
  have hfree : ∀ v, ρ (ι z) v = v → v = 0 := by
    let := hi
    have hzn : (zpowers (z : TripleSeven)).Normal := by rw [hgen]; infer_instance
    exact RankTwo.fixed_free_of_faithful_irreducible_normal_three
      (ρ.comp ι) (h.faithful.comp hι) z hz3 hzn
  have hcent := small_actor_centralizes_normal_three ρ h.faithful (ι z)
    ((orderOf_injective ι hι z).trans hz3) hcn hfree hd A hA hr hsmall
  rw [hcgen] at hcent
  intro a ha
  rw [← hrange]
  let := hA.2
  exact involution_mem_range ι hι hn ρ h.faithful hi a
    (elemPow_eq_one_of_isElementaryAbelian a ha) (hcent ha)

/-- The full ambient cubic bound restricts to the genuine triple-seven action. -/
theorem tripleSevenRestrictionBound : RecognitionInputs.TripleSevenRestrictionBound.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_bound
  have hAL := tripleSeven_small_actor_le ρ h e A hA hd
  let B := A.subgroupOf L
  let C := B.map e.toMonoidHom
  have hB : IsElementaryTwo B := by
    let := hA.2
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAL⟩
    intro hz
    apply hA.1
    change A.subgroupOf L = ⊥ at hz
    rw [← map_subgroupOf_eq_of_le hAL, hz, Subgroup.map_bot]
  have hC : IsElementaryTwo C := by
    let := hB.2
    exact ⟨fun hz => hB.1 ((B.map_eq_bot_iff_of_injective e.injective).mp hz),
      IsElementaryAbelian.map _⟩
  apply (cubicRatio_le_nat_iff _ 2).mpr
  refine ⟨C, hC, ?_, ?_⟩
  · rintro a ⟨a, ha, rfl⟩ b ⟨b, hb, rfl⟩ c ⟨c, hc', rfl⟩ v
    change displacement ρ (e.symm (e a))
      (displacement ρ (e.symm (e b)) (displacement ρ (e.symm (e c)) v)) = 0
    rw [e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]
    exact hc a ha b hb c hc' v
  · have hm : C.map e.symm.toMonoidHom = B := by
      rw [map_map]
      have hh : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L := by
        apply MonoidHom.ext
        intro x
        exact e.symm_apply_apply x
      rw [hh, map_id]
    have he : fixedCodim ((ρ.comp L.subtype).comp e.symm.toMonoidHom) C =
        fixedCodim ρ A := by
      rw [fixedCodim, fixedSpace_comp_map, hm]
      exact fixedCodim_subgroupOf ρ hAL
    rw [he, rank_map_injective _ e.injective, rank_subgroupOf hAL]
    exact hd

end CFSG.Quasithin.ChapterK.Alternating
