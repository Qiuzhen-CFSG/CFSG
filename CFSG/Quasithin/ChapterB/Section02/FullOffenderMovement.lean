module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.FullOffenderMovement
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
/-!
# Full best-offender movement for an internal reduced module

The images of the original maximum elementary subgroups are best offenders
and generate exactly the image of J(T). The local full-family theorem therefore
extends original Thompson movement to J(T*,V), on the literal centralizer
quotient action. Relative subnormality is transported through the actual map.

Source: Aschbacher--Smith B.2.7 and C.1.27, pp.76,133.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
universe u v
variable {G : Type u} [Group G] [Finite G] {Q : Type v} [Group Q] [Finite Q]

omit [Finite G] [Finite Q] in
private theorem image_subnormal_in_local_join (q : G →* Q) (K T : Subgroup G)
    (hs : (K.subgroupOf (K ⊔ T)).IsSubnormal) :
    ((K.map q).subgroupOf (K.map q ⊔ T.map q)).IsSubnormal := by
  let H := K ⊔ T
  have he : (K.subgroupOf H).map (q.subgroupMap H) = (K.map q).subgroupOf (H.map q) := by
    apply map_injective (H.map q).subtype_injective
    have hh : (H.map q).subtype.comp (q.subgroupMap H) = q.comp H.subtype := rfl
    rw [map_map,hh,← map_map,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (map_mono (show K ≤ H from le_sup_left))]
  have hh := hs.map (q.subgroupMap_surjective H)
  rw [he] at hh
  change ((K.map q).subgroupOf ((K ⊔ T).map q)).IsSubnormal at hh
  rw [Subgroup.map_sup] at hh
  exact hh

/-- Original Thompson movement gives the precise B.1.13 full-offender premise. -/
theorem internal_full_best_movement
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G)) (K T : Subgroup G)
    (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hs : (K.subgroupOf (K ⊔ T)).IsSubnormal)
    (hkind : IsQuasisimple (K.map q) ∨ Nat.card (K.map q) = 3)
    (hm : K = ⁅K,elementaryAbelianMaxJ T⁆) :
    let ρ := NormalElementaryQuotient.representation V q hq hk;
    K.map q = ⁅K.map q, generatedBy {A | IsBestOffender ρ A} (T.map q)⁆ := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  have hP : ∀ A ∈ maxOffenderImages T V q, IsBestOffender ρ A ∧ A ≤ T.map q := by
    rintro _ ⟨A,hA,rfl,hn⟩
    exact ⟨(show IsFFOffender V q T A from ⟨hA,hn⟩).isBestOffender V q hq hk hVT,
      map_mono hA.1⟩
  have hmove : K.map q = ⁅K.map q,generatedBy (maxOffenderImages T V q) ⊤⁆ := by
    rw [← maxOffenderImages_generated T V q,← map_commutator,← hm]
  exact ThreeConjugates.full_best_movement_of_family ρ
    (NormalElementaryQuotient.representation_injective V q hq hk)
    (K.map q) (T.map q) hkind (image_subnormal_in_local_join q K T hs) (hT.map q)
    (maxOffenderImages T V q) hP hmove
end CFSG.Quasithin.ChapterB
