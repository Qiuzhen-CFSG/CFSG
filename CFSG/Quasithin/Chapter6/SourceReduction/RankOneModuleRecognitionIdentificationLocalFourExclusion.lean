module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalMinimal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGeneration
public import Theory.ElementaryAbelian.Injective

/-!
# Excluding the order-four core intersection

The actual H-star subgroup Y supplied by the marked A₇ action has a normal
A₅ subgroup in its image, and the original elementary layer maps onto a full
Sylow four-group of that A₅. Transport the A₅ Sylow-normalizer geometry to
this image and retain the elementary lift through both solvable kernels
in the E-member definition. The resulting generation obstruction gives
n(Y) ≠ 1, contradicting Hypothesis 6.1.1 on this same Y.

Thus the order-four alternative is excluded. With the earlier 6.2.8 layer
escape, the actual core intersection has order eight. The escape remains
explicit; no LocalAnalysis or later identification is used.

Source: Aschbacher--Smith, 6.2.11, final paragraph, printed p.686. The lifted
actor supplies the needed generation contradiction without the invalid
general quotient-only numerical inference from E.2.2.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction

private theorem five_lift_not_generation_one
    {E : Type*} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 7))
    (B : Subgroup (alternatingGroup (Fin 7)))
    (e : B ≃* alternatingGroup (Fin 5))
    (hB : B ≤ f.range) (hnB : f.range ≤ normalizer (B : Set (alternatingGroup (Fin 7))))
    (Q : Sylow 2 B) (A : Subgroup E) [IsElementaryAbelian 2 A]
    (hA : A.map f = (Q : Subgroup B).map B.subtype) :
    ChapterE.generationParameter E ≠ 1 := by
  let D := f.range
  let B' := B.subgroupOf D
  let eB := (subgroupOfEquivOfLe hB).trans e
  let : B'.Normal := (normal_subgroupOf_iff_le_normalizer hB).mpr hnB
  let : IsSimpleGroup B' := eB.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hBs : ¬ Group.IsSolvable B' := Group.IsPerfect.not_isSolvable B'
  let k : E →* D := f.rangeRestrict
  let eQ := (subgroupOfEquivOfLe hB).symm
  let Q' := Q.mapSurjective (f := eQ.toMonoidHom) eQ.surjective
  have hmap : (Q' : Subgroup B').map B'.subtype = A.map k := by
    apply (map_injective D.subtype_injective)
    rw [map_map,map_map]
    change ((Q : Subgroup B).map eQ.toMonoidHom).map (D.subtype.comp B'.subtype) =
      A.map (D.subtype.comp k)
    rw [map_map]
    change (Q : Subgroup B).map B.subtype = A.map f
    exact hA.symm
  have hAel : IsElementaryAbelian 2 (A.map k) := IsElementaryAbelian.map k
  let : IsElementaryAbelian 2 ((Q' : Subgroup B').map B'.subtype) := hmap.symm ▸ hAel
  let eA := (Q' : Subgroup B').equivMapOfInjective B'.subtype B'.subtype_injective
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.of_injective eA.toMonoidHom eA.injective
  have hcB : Nat.card B' = 60 := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcQ : Nat.card Q' = 4 := by
    rw [Q'.card_eq_multiplicity,hcB]
    decide +kernel
  have hr : 1 < Group.rank Q' := by
    have hd := card_dvd_exponent_pow_rank' Q'
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Q'))
    have hl := Nat.le_of_dvd (by positivity : 0 < 2 ^ Group.rank Q') hd
    rw [hcQ] at hl
    by_contra hn
    have hu := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt hn)
    norm_num at hu
    omega
  have hproper (K : Subgroup B') (hQK : (Q' : Subgroup B') ≤ K) (hK : K ≠ ⊤) :
      K ≤ normalizer (Q' : Set B') := by
    apply (map_le_map_iff_of_injective (f := eB.toMonoidHom) eB.injective).mp
    change K.map eB.toMonoidHom ≤ (normalizer ((Q' : Subgroup B') : Set B')).map eB.toMonoidHom
    rw [map_equiv_normalizer_eq (Q' : Subgroup B') eB]
    apply Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
      (Q'.mapSurjective eB.surjective) (K.map eB.toMonoidHom) (map_mono hQK)
    intro he
    apply hK
    apply (map_injective (f := eB.toMonoidHom) eB.injective)
    rw [he,map_top_of_surjective eB.toMonoidHom eB.surjective]
  have hn : normalizer (Q' : Set B') ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map eB.toMonoidHom) he
    change (normalizer ((Q' : Subgroup B') : Set B')).map eB.toMonoidHom = (⊤ : Subgroup B').map eB.toMonoidHom at hh
    rw [map_equiv_normalizer_eq (Q' : Subgroup B') eB,map_top_of_surjective eB.toMonoidHom eB.surjective] at hh
    exact (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_normalizer_isCoatom
      (Q'.mapSurjective eB.surjective)).ne_top hh
  exact not_generation_one_of_elementary_sylow_lift k f.rangeRestrict_surjective
    B' hBs Q' hr hproper hn A hmap.symm

variable {G : Type*} [Group G] [Finite G] {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The original order-four branch contradicts generation one on its actual H-star subgroup. -/
theorem four_intersection_false
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hNM : normalizer (L : Set G) ≤ M)
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) : False := by
  obtain ⟨Y,hY,hYX,_hi,q,_hq,_hk,B,⟨eB⟩,hJ,hSN,Q,hQ⟩ :=
    four_exists_hstar_index_five_seed h hnatural hz ho hP hplane hNL hNM hcard
  let X := fourOvergroup (P : Subgroup G) L z
  let f : Y →* alternatingGroup (Fin 7) := q.comp (inclusion hYX)
  have hrange : f.range = (Y.subgroupOf X).map q := by
    ext a
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨inclusion hYX y,y.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hB : B ≤ f.range := by rw [hrange,hJ]; exact le_sup_left
  have hnB : f.range ≤ normalizer (B : Set (alternatingGroup (Fin 7))) := by
    rw [hrange,hJ]
    exact sup_le B.le_normalizer hSN
  have hVY : layer L R ≤ Y := h.layer_le_T.trans hY.1.1.2
  let A := (layer L R).subgroupOf Y
  let := h.layer_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVY
  have hA : A.map f = (Q : Subgroup B).map B.subtype := by
    rw [hQ]
    change A.map (q.comp (inclusion hYX)) = _
    rw [← map_map]
    congr 1
    apply (map_injective X.subtype_injective)
    rw [map_map,map_subgroupOf_eq_of_le (hVY.trans hYX)]
    change A.map Y.subtype = layer L R
    exact map_subgroupOf_eq_of_le hVY
  exact five_lift_not_generation_one f B eB hB hnB Q A hA (h.generation_one Y hY)

/-- With the earlier source 6.2.8 escape, only the order-eight core
intersection remains. The contrary order-four branch is now discharged. -/
theorem core_card_eight_of_layer_escape
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hNM : normalizer (L : Set G) ≤ M)
    (hescape : ¬ layer L R ≤ (Centralizer z).pCoreIn 2) :
    Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 8 :=
  (core_card_dichotomy h hnatural hz ho hP hescape).resolve_left
    (four_intersection_false h hnatural hz ho hP hplane hNL hNM)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
