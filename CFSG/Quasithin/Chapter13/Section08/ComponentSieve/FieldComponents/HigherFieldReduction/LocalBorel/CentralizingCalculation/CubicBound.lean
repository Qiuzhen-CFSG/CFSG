module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Core
public import Theory.GroupAction.CyclicAuxiliaryIndex.Transport

/-!
# From the local index three to the marked commutator bound

The bound is first proved in G for [B,⟨t⟩], with B_C allowed outside B.
Passing through H → H/O₂(H) can only decrease the intrinsic two-core
quotient order. The equivariant embedding K* → H* then identifies that
image with the full cyclic-action commutator of the original marked actor.

The source index and abelianness of the Borel torus remain explicit inputs.
They are local-calculation obligations, not consequences of this transport.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
open TorusModels.Assembly Theory.GroupAction.CyclicAuxiliaryIndex
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The source star image commutes with the literal cyclic commutator. -/
theorem starImage_cyclic_commutator (H B : Subgroup G) (hBH : B ≤ H) (t : H) :
    Source.starImage H ⁅B, zpowers t.val⁆ =
      ⁅Source.starImage H B, zpowers (QuotientGroup.mk' (pCore 2 H) t)⁆ := by
  have hm : (⁅B.subgroupOf H, zpowers t⁆ : Subgroup H).map H.subtype =
      ⁅B, zpowers t.val⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hBH, MonoidHom.map_zpowers]
    rfl
  rw [Source.starImage, ← hm, ← comap_subtype,
    comap_map_eq_self_of_injective H.subtype_injective, map_commutator, MonoidHom.map_zpowers]
  rfl

/-- Quotienting inside H cannot increase the two-core quotient order. -/
theorem starImage_twoCore_quotient_card_le (H D : Subgroup G) (hDH : D ≤ H) :
    Nat.card (Source.starImage H D ⧸ pCore 2 (Source.starImage H D)) ≤
      Nat.card (D ⧸ pCore 2 D) := by
  let f := starHom H D hDH
  have hh := quotient_twoCore_card_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  change Nat.card ((starHom H D hDH).range ⧸ pCore 2 (starHom H D hDH).range) ≤ _ at hh
  rw [range_starHom H D hDH] at hh
  exact hh

/-- Retain the original t when passing the local commutator bound to K*. -/
theorem markedActor_commutatorOrder_le
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (t : H) (ht : t.val ∈ T) (m : ℕ)
    (hsmall : let D : Subgroup G := ⁅borel H K T hKH hT, zpowers t.val⁆
      Nat.card (D ⧸ pCore 2 D) ≤ m) :
    commutatorOrder (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht) ≤ m := by
  let B := borel H K T hKH hT
  let D : Subgroup G := ⁅B, zpowers t.val⁆
  let R := residualAt (sourceSylow H K T hT)
  let a := markedActor H K T t ht
  let f := (Source.starImage H K).subtype
  have hBH : B ≤ H := (borel_le_component H K T hKH hT).trans hKH
  have hDH : D ≤ H := (Subgroup.commutator_le_sup B (zpowers t.val)).trans (sup_le hBH (zpowers_le.mpr t.property))
  have hR : R.map f = Source.starImage H B := (borel_star_intrinsic H K T hKH hT).symm
  have hstable : R.map a.toMonoidHom = R := residualAt_stable _ _ (starActor_stable H K T hT _)
  have himage : (commutatorSubgroup (zpowers a) (Source.starImage H K) R).map f =
      Source.starImage H D := by
    rw [map_cyclic_commutator_conjugation f a (QuotientGroup.mk' (pCore 2 H) t) R hstable
      (fun _ => rfl), hR, ← starImage_cyclic_commutator H B hBH t]
  calc
    commutatorOrder R a = Nat.card
        ((commutatorSubgroup (zpowers a) (Source.starImage H K) R).map f ⧸
          pCore 2 ((commutatorSubgroup (zpowers a) (Source.starImage H K) R).map f)) :=
      quotient_twoCore_card_map_of_injective f (Source.starImage H K).subtype_injective _
    _ = Nat.card (Source.starImage H D ⧸ pCore 2 (Source.starImage H D)) := by rw [himage]
    _ ≤ Nat.card (D ⧸ pCore 2 D) := starImage_twoCore_quotient_card_le H D hDH
    _ ≤ m := hsmall

/-- The precise source index gives the small marked quotient. All normalization
and B_C displacement premises are derived, with the intrinsic cores intact. -/
theorem markedActor_commutatorOrder_le_three_of_index
    (H K T L₁ L X : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hJL : borel H K T hKH hT ⊔ L₁ ≤ normalizer (L : Set G))
    (hNB : L₁ ⊔ T ≤ normalizer (borel H K T hKH hT : Set G))
    (hTL₁ : T ≤ normalizer (L₁ : Set G))
    (habelian : ⁅borel H K T hKH hT, borel H K T hKH hT⁆ ≤ (borel H K T hKH hT).pCoreIn 2)
    (hindex : (centralizingResidual (borel H K T hKH hT) L₁ L ⊔
      (borel H K T hKH hT).pCoreIn 2).relIndex (borel H K T hKH hT ⊔ X) = 3)
    (t : H) (ht : t.val ∈ T) (htL : t.val ∈ L) :
    commutatorOrder (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht) ≤ 3 := by
  let B := borel H K T hKH hT
  let C := centralizingResidual B L₁ L
  have hJB : B ⊔ L₁ ≤ normalizer (B : Set G) :=
    sup_le B.le_normalizer (le_sup_left.trans hNB)
  have hTJ : T ≤ normalizer ((B ⊔ L₁ : Subgroup G) : Set G) :=
    (le_inf (le_sup_right.trans hNB) hTL₁).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply markedActor_commutatorOrder_le H K T hKH hT t ht 3
  exact (commutator_twoCore_card_le B C X
    (borel_normalizes_centralizingResidual B L₁ L hJL)
    ((centralizingResidual_le B L₁ L).trans hJB) habelian t.val
    (hNB (mem_sup_right ht))
    (centralizingResidual_commutator_core B L₁ L hJL t.val htL (hTJ ht))).trans_eq hindex

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
