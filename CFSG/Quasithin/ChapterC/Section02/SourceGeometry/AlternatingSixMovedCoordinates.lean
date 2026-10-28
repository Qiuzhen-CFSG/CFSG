module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedSource
public import Theory.Representation.BinaryPermutationMulAction
/-!
# Natural coordinates on the actual order-sixteen A₆ moved star module

The B.5 source theorem gives the natural A₆ action on the quotient of the
moved star module by its fixed subspace. If the original moved module has
order sixteen, that surjective quotient map is bijective. Its inverse-free
construction retains the literal conjugation action and the specified star
marking. The ambient-image theorem is the interface used by the generated
parabolic's rank-three span argument.

Source: Aschbacher--Smith B.5.1, C.2.7, and 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

theorem star_alternatingSix_natural_coordinates
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (⁅starV K R,K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G)) = 16) :
    let W := ⁅starV K R,K.subgroupOf (K ⊔ R)⁆
    ∃ f : K →* alternatingGroup (Fin 6), Function.Surjective f ∧
      ∃ E : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
        ∀ (k : K) (w : W)
          (hw : (⟨k,mem_sup_left k.property⟩ : (K ⊔ R : Subgroup G)) * w.val *
            (⟨k,mem_sup_left k.property⟩ : (K ⊔ R : Subgroup G))⁻¹ ∈ W),
          (E ⟨_,hw⟩).toAdd = BinaryPermutation.naturalRepresentation (Fin 6)
            (f k).val (E w).toAdd := by
  let V := starV K R
  let C := K.subgroupOf (K ⊔ R)
  let W := ⁅V,C⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left V C)) (inclusion_injective _)
  let q := QuotientGroup.mk' (starKernel K R)
  let J := offenderSubgroup (starRepresentation K R)
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  obtain ⟨_,⟨m⟩⟩ := AlternatingSixMovedModel.source_natural _ c
    ((subgroupOfEquivOfLe hCJ).trans e)
  let s := c.sectionData
  have hs : s.space.toSubmodule =
      subspaceCommutator (starRepresentation K R) ⊤ (C.map q) := by
    rw [s.space_eq]
    change subspaceCommutator ((starRepresentation K R).comp J.subtype) ⊤
      ((starImage K R K).subgroupOf J) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  let a : Additive W ≃ₗ[ZMod 2] s.space.toSubmodule :=
    (NormalElementaryQuotient.movedEquiv V q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) C).trans (LinearEquiv.ofEq _ _ hs.symm)
  let p := m.linearEquiv.toLinearMap.comp (s.central.toSubmodule.mkQ.comp a.toLinearMap)
  have hp : Function.Surjective p := m.linearEquiv.surjective.comp
    ((Submodule.mkQ_surjective _).comp a.surjective)
  have hnat : Nat.card (BinaryPermutation.natural (Fin 6)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  have hbij : Function.Bijective p := (Nat.bijective_iff_surjective_and_card p).mpr
    ⟨hp,(Nat.card_congr Additive.toMul).trans (hc.trans hnat.symm)⟩
  let E := LinearEquiv.ofBijective p hbij
  let f := m.groupEquiv.toMonoidHom.comp
    ((subgroupOfEquivOfLe hCJ).symm.toMonoidHom.comp (toStarImage K R))
  have hf : Function.Surjective f := m.groupEquiv.surjective.comp
    ((subgroupOfEquivOfLe hCJ).symm.surjective.comp (toStarImage_surjective K R))
  refine ⟨f,hf,E.toAddEquiv.toMultiplicativeRight,?_⟩
  intro k w hw
  let z := (subgroupOfEquivOfLe hCJ).symm (toStarImage K R k)
  have ha : a (Additive.ofMul (⟨_,hw⟩ : W)) =
      s.space.toRepresentation z (a (Additive.ofMul w)) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      ⟨k,mem_sup_left k.property⟩
      (Additive.ofMul ⟨w.val,(commutator_le_left V C) w.property⟩)).symm
  have he := m.intertwines z (s.central.toSubmodule.mkQ (a (Additive.ofMul w)))
  exact (congrArg (fun v => m.linearEquiv (s.central.toSubmodule.mkQ v)) ha).trans he

/-- Coordinates on the literal ambient image of the moved star module. -/
theorem star_alternatingSix_natural_coordinates_ambient
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6))
    (hc : Nat.card ((⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map
      (K ⊔ R : Subgroup G).subtype) = 16) :
    let W := (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map (K ⊔ R : Subgroup G).subtype
    ∃ f : K →* alternatingGroup (Fin 6), Function.Surjective f ∧
      ∃ E : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
        ∀ (k : K) (w : W) (hw : (k : G) * w.val * (k : G)⁻¹ ∈ W),
          (E ⟨_,hw⟩).toAdd = BinaryPermutation.naturalRepresentation (Fin 6)
            (f k).val (E w).toAdd := by
  let KR := K ⊔ R
  let W0 := ⁅starV K R,K.subgroupOf KR⁆
  let W := W0.map KR.subtype
  have hc0 : Nat.card W0 = 16 := by
    simpa only [card_map_of_injective (subtype_injective _)] using hc
  obtain ⟨f,hf,E,ha⟩ := star_alternatingSix_natural_coordinates h e hc0
  let em := W0.equivMapOfInjective KR.subtype KR.subtype_injective
  refine ⟨f,hf,em.symm.trans E,?_⟩
  intro k w hw
  let x := em.symm w
  have hx : ((x.val : KR) : G) = w.val :=
    congrArg Subtype.val (em.apply_symm_apply w)
  have hw0 : (⟨k,mem_sup_left k.property⟩ : KR) * x.val *
      (⟨k,mem_sup_left k.property⟩ : KR)⁻¹ ∈ W0 := by
    apply (comap_map_eq_self_of_injective KR.subtype_injective W0).le
    change (k : G) * ((x.val : KR) : G) * (k : G)⁻¹ ∈ W
    rwa [hx]
  have he : em.symm (⟨_,hw⟩ : W) = ⟨_,hw0⟩ := by
    apply em.injective
    rw [em.apply_symm_apply]
    apply Subtype.ext
    change (k : G) * w.val * (k : G)⁻¹ =
      (k : G) * ((x.val : KR) : G) * (k : G)⁻¹
    rw [hx]
  exact (congrArg (fun y => (E y).toAdd) he).trans (ha k x hw0)

end CFSG.Quasithin.ChapterC.C27Source
