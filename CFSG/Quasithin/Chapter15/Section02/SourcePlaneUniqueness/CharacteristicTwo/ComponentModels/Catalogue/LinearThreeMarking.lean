module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearFlags
public import Theory.SpecificGroups.SL3.RadicalNormalizer

/-!
# Marked maximal parabolics in both linear-three source rows

For a natural SL3 moved section over F2, dimension excludes the exceptional
outer actors. At larger field orders, the component order exceeds every
such actor. Thus the original Thompson image is inside the component.
The doubled-natural row supplies this containment through its whole-actor
clause. No Thompson-containment hypothesis remains in either row theorem.

The actual marking is the radical-intersection normalizer. The non-Sylow
source conclusion excludes the Borel alternative, leaving a maximal
parabolic. In degree one the field is identified with F2; otherwise the
original field and its full scalar center are retained. Both rows are
applied to the same selected X, R = O2(NI), and NI = M intersect I.

This proves the marked parabolic clause of C.2.7(g) for these source rows.
The full core-quotient identification, C.1.34 MS description, and elimination
of the remaining non-linear-three rows are still required for 15.2.23.

Source: Aschbacher--Smith B.5.1, pp.99--103; C.2.7, pp.145--147; original
15.2.23, pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

private theorem linearThree_card_large (F : BinaryField) (hn : 1 < F.degree) :
    40320 < Nat.card SL(3,F.Carrier) := by
  have hc : Nat.card SL(3,F.Carrier) =
      Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
        (Nat.card F.Carrier ^ 2 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F.Carrier)),
      Atlas.ExceptionalSupport.card_sl_center]
    exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier
  have hq : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  rw [hc]
  have hh := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  exact lt_of_lt_of_le (by norm_num : 40320 < 4^3*(4^3-1)*(4^2-1)) hh

variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

/-- The actual natural moved section puts the original Thompson image in X*. -/
theorem naturalThree_thompson_inner
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    (F : BinaryField)
    (a : ActionEquiv (s.action.comp
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))).subtype)
        (linearNatural F 3))
    (hext : (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)) = ⊤ ∨
      (∀ T : Sylow 2 (offenderSubgroup (starRepresentation X R)),
        (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)) ⊔
          (T : Subgroup _) = ⊤) ∧ OuterNaturalAction s.action) :
    starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X := by
  by_cases hn : 1 < F.degree
  · let : (X.subgroupOf (X ⊔ R)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
    apply star_thompson_le_component_of_large_order (source_join_input h)
    rw [Nat.card_congr ((subgroupOfEquivOfLe hCJ).symm.trans a.groupEquiv).toEquiv]
    exact linearThree_card_large F hn
  have hn : F.degree = 1 := by have := F.degree_pos; omega
  have ht : (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)) = ⊤ := by
    rcases hext with ht | ⟨_,hext⟩
    · exact ht
    exfalso
    have hdF : Module.finrank (ZMod 2) F.Carrier = 1 := by
      apply Nat.pow_right_injective (by decide : 2 ≤ 2)
      calc
        2 ^ Module.finrank (ZMod 2) F.Carrier = Nat.card F.Carrier := by
          simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)).symm
        _ = 2^1 := by rw [F.card_eq,hn]
    have hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 3 := by
      rw [a.linearEquiv.finrank_eq,Module.finrank_pi_fintype]
      simp [hdF]
    rcases hext with ⟨n,hn5,hn8,⟨b⟩⟩ | ⟨b⟩
    · have hh := b.linearEquiv.finrank_eq
      rw [hd] at hh
      interval_cases n <;>
        first
        | rw [BinaryPermutation.finrank_natural_odd (Fin _) (by decide)] at hh; contradiction
        | rw [BinaryPermutation.finrank_natural_even (Fin _) (by decide)] at hh; contradiction
    · obtain ⟨b⟩ := b
      have hh := b.linearEquiv.finrank_eq
      rw [hd,Atlas.G2.Natural.finrank_space] at hh
      contradiction
  exact (star_thompson_le_offenderSubgroup_from_source h).trans (subgroupOf_eq_top.mp ht)

variable {H K M : Subgroup G}

private theorem standard_linearThree_parabolic
    {F : Type*} [Field F] [Finite F] {A : Type*} [Group A]
    (P : Subgroup A) (e : A ≃* SL(3,F))
    (he : P.map e.toMonoidHom = Matrix.PSL3.LinearThree.pointParabolicSL F ∨
      P.map e.toMonoidHom = Matrix.PSL3.LinearThree.lineParabolicSL F) :
    IsLinearMaximalParabolic P 3 F := by
  rcases he with he | he
  · let W : Submodule F (Fin 3 → F) := {
      carrier := {v | v 1 = 0 ∧ v 2 = 0}
      zero_mem' := ⟨rfl,rfl⟩
      add_mem' := by rintro u v ⟨h1,h2⟩ ⟨k1,k2⟩; simp_all
      smul_mem' := by rintro a v ⟨h1,h2⟩; simp_all }
    refine ⟨e,W,?_,?_,he.trans ?_⟩
    · intro hz
      have hh : (![1,0,0] : Fin 3 → F) ∈ W := by constructor <;> rfl
      rw [hz,Submodule.mem_bot] at hh
      have := congrFun hh 0
      simp at this
    · intro ht
      have hh : (![0,1,0] : Fin 3 → F) ∈ W := ht ▸ Submodule.mem_top
      have := hh.1
      simp at this
    · ext g
      rw [Matrix.PSL3.LinearThree.pointParabolicSL,linearStabilizer,
        Subgroup.mem_comap,Submodule.stabilizer_coe,
        MulAction.mem_stabilizer_set,MulAction.mem_stabilizer_set]
      rfl
  · let W : Submodule F (Fin 3 → F) := {
      carrier := {v | v 2 = 0}
      zero_mem' := rfl
      add_mem' := by intro u v hu hv; change u 2 + v 2 = 0; rw [hu,hv,add_zero]
      smul_mem' := by intro a v hv; change a * v 2 = 0; rw [hv,mul_zero] }
    refine ⟨e,W,?_,?_,he.trans ?_⟩
    · intro hz
      have hh : (![1,0,0] : Fin 3 → F) ∈ W := rfl
      rw [hz,Submodule.mem_bot] at hh
      have := congrFun hh 0
      simp at this
    · intro ht
      have hh : (![0,0,1] : Fin 3 → F) ∈ W := ht ▸ Submodule.mem_top
      simp [W] at hh
    · ext g
      rw [Matrix.PSL3.LinearThree.lineParabolicSL,linearStabilizer,
        Subgroup.mem_comap,Submodule.stabilizer_coe,
        MulAction.mem_stabilizer_set,MulAction.mem_stabilizer_set]
      rfl

/-- The nonbinary radical normalizer is a maximal parabolic, with the Sylow alternative excluded. -/
theorem nonbinaryThree_marked_parabolic_of_thompson_inner
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hM : M ≤ normalizer (R : Set G)) (hc : ¬ ChapterC.IsChiBlock K)
    (hi : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R K)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : starImage K R K ≃* SL(3,F.Carrier)) :
    IsLinearMaximalParabolic ((starM K R M).subgroupOf (starImage K R K)) 3 F.Carrier := by
  let C := starImage K R K
  let U := (starImage K R R).subgroupOf C
  obtain ⟨hr,he⟩ := marked_radical_normalizer h hM hi
  rcases Matrix.PSL3.LinearThree.RadicalNormalizer.radical_normalizer_parabolic_or_sylow
    (U.map e.toMonoidHom) (hr.map_equiv e) hn F.card_eq with ⟨a,ha⟩ | ⟨S,hS⟩
  · apply standard_linearThree_parabolic _
      (e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a))
    have hm : ((starM K R M).subgroupOf C).map
        (e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)).toMonoidHom =
        (normalizer (U.map e.toMonoidHom : Set SL(3,F.Carrier))).map
          (Matrix.HigherLinear.SubspaceTransport.slConj a).toMonoidHom := by
      change ((starM K R M).subgroupOf C).map
        ((Matrix.HigherLinear.SubspaceTransport.slConj a).toMonoidHom.comp e.toMonoidHom) = _
      rw [←map_map,he,map_equiv_normalizer_eq]
    rcases ha with ha | ha
    · exact Or.inl (hm.trans ha)
    · exact Or.inr (hm.trans ha)
  · apply (star_radical_not_sylow h hc ?_).elim
    refine ⟨S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,?_⟩
    change (S : Subgroup SL(3,F.Carrier)).map e.symm.toMonoidHom ≤ U
    rw [hS]
    simp [Subgroup.map_map]

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue

namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

include hsource in
/-- The natural row identifies the literal radical normalizer on the selected escaping component. -/
theorem normalized_component_naturalThree_normalizer
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (F : BinaryField)
    (a : ActionEquiv (s.action.comp
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))).subtype)
        (linearNatural F 3))
    (hext : (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) = ⊤ ∨
      (∀ T : Sylow 2 (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))),
        (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
          (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) ⊔
          (T : Subgroup _) = ⊤) ∧ OuterNaturalAction s.action) :
    let R := (M ⊓ I).pCoreIn 2
    IsPRadical 2 ((starImage X R R).subgroupOf (starImage X R X)) ∧
      (starM X R (M ⊓ I)).subgroupOf (starImage X R X) =
        normalizer ((starImage X R R).subgroupOf (starImage X R X) :
          Set (starImage X R X)) := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  apply marked_radical_normalizer h ?_ (naturalThree_thompson_inner h hCJ s F a hext)
  exact (M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G)))

include hsource in
/-- The nonbinary star model supplies the actual selected component's maximal parabolic. -/
theorem normalized_component_nonbinaryThree_parabolic
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(3,F.Carrier)) :
    IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F.Carrier := by
  let R := (M ⊓ I).pCoreIn 2
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  let : (X.subgroupOf (X ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer selection.radical_normalizes)
  have hi : starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X := by
    apply star_thompson_le_component_of_large_order (source_join_input h)
    rw [Nat.card_congr e.toEquiv]
    exact linearThree_card_large F hn
  apply nonbinaryThree_marked_parabolic_of_thompson_inner h ?_
    (selection.toSelected.not_chi hno) hi F hn e
  exact (M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G)))

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue

namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Subgroup Theory.GroupTheory Stellmacher
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- A positive-rank flag in dimension three has one member, giving the binary maximal parabolic. -/
theorem binaryThree_marked_parabolic_of_thompson_inner
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hM : M ≤ normalizer (R : Set G)) (hc : ¬ ChapterC.IsChiBlock K)
    (hi : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R K)
    (e : starImage K R K ≃* SL(3,ZMod 2)) :
    IsLinearMaximalParabolic ((starM K R M).subgroupOf (starImage K R K)) 3 (ZMod 2) := by
  obtain ⟨a,k,hk,hbound,f,hf⟩ := binary_marked_parabolic_of_thompson_inner h hM hc hi (by decide) e
  have hk : k = 1 := by omega
  subst k
  let b := BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)
  refine ⟨a.trans b,f.space 0,f.nonzero 0,f.proper 0,?_⟩
  change ((starM K R M).subgroupOf (starImage K R K)).map
    (b.toMonoidHom.comp a.toMonoidHom) = _
  rw [←map_map,hf,map_map]
  have hb : b.toMonoidHom.comp (QuotientGroup.mk' (center SL(3,ZMod 2))) =
      MonoidHom.id SL(3,ZMod 2) := by
    apply MonoidHom.ext
    intro g
    exact b.apply_symm_apply g
  rw [hb,Subgroup.map_id]
  simp [LinearFlag.stabilizer]

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue

namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

private theorem linearThree_marked_choice
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hN : N ≤ normalizer (R : Set G)) (hc : ¬ ChapterC.IsChiBlock X)
    (hi : starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X)
    (F : BinaryField) (e : starImage X R X ≃* SL(3,F.Carrier)) :
    (F.degree = 1 ∧ IsLinearMaximalParabolic
      ((starM X R N).subgroupOf (starImage X R X)) 3 (ZMod 2)) ∨
    (1 < F.degree ∧ IsLinearMaximalParabolic
      ((starM X R N).subgroupOf (starImage X R X)) 3 F.Carrier) := by
  by_cases hn : 1 < F.degree
  · exact Or.inr ⟨hn,nonbinaryThree_marked_parabolic_of_thompson_inner h hN hc hi F hn e⟩
  have hn : F.degree = 1 := by have := F.degree_pos; omega
  let : Fintype F.Carrier := Fintype.ofFinite _
  let f : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,F.card_eq,hn]
    simp)
  exact Or.inl ⟨hn,binaryThree_marked_parabolic_of_thompson_inner h hN hc hi
    (e.trans (Atlas.fieldEquivSL 3 f))⟩

/-- Recognize the marked parabolic from the actual natural B.5.1 row, without a Thompson premise. -/
theorem naturalThree_marked_parabolic
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hN : N ≤ normalizer (R : Set G)) (hc : ¬ ChapterC.IsChiBlock X)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    (F : BinaryField)
    (a : ActionEquiv (s.action.comp
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))).subtype)
        (linearNatural F 3))
    (hext : (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)) = ⊤ ∨
      (∀ T : Sylow 2 (offenderSubgroup (starRepresentation X R)),
        (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)) ⊔
          (T : Subgroup _) = ⊤) ∧ OuterNaturalAction s.action) :
    (F.degree = 1 ∧ IsLinearMaximalParabolic
      ((starM X R N).subgroupOf (starImage X R X)) 3 (ZMod 2)) ∨
    (1 < F.degree ∧ IsLinearMaximalParabolic
      ((starM X R N).subgroupOf (starImage X R X)) 3 F.Carrier) :=
  linearThree_marked_choice h hN hc (naturalThree_thompson_inner h hCJ s F a hext) F
    ((subgroupOfEquivOfLe hCJ).symm.trans a.groupEquiv)

/-- Recognize the marked parabolic from the doubled-natural B.5.1 row, using its whole-actor clause. -/
theorem doubleThree_marked_parabolic
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hN : N ≤ normalizer (R : Set G)) (hc : ¬ ChapterC.IsChiBlock X)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    (F : BinaryField)
    (ht : (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)) = ⊤)
    (a : ActionEquiv (s.space.toRepresentation.comp
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))).subtype)
        (repeated (linearNatural F 3) 2)) :
    (F.degree = 1 ∧ IsLinearMaximalParabolic
      ((starM X R N).subgroupOf (starImage X R X)) 3 (ZMod 2)) ∨
    (1 < F.degree ∧ IsLinearMaximalParabolic
      ((starM X R N).subgroupOf (starImage X R X)) 3 F.Carrier) :=
  linearThree_marked_choice h hN hc
    ((star_thompson_le_offenderSubgroup_from_source h).trans (subgroupOf_eq_top.mp ht)) F
    ((subgroupOfEquivOfLe hCJ).symm.trans a.groupEquiv)

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue


namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

include hsource in
/-- Apply natural-row parabolic recognition to the original selected X, R and NI. -/
theorem normalized_component_naturalThree_parabolic
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (F : BinaryField)
    (a : ActionEquiv (s.action.comp
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))).subtype)
        (linearNatural F 3))
    (hext : (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) = ⊤ ∨
      (∀ T : Sylow 2 (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))),
        (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
          (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) ⊔
          (T : Subgroup _) = ⊤) ∧ OuterNaturalAction s.action) :
    let R := (M ⊓ I).pCoreIn 2
    (F.degree = 1 ∧ IsLinearMaximalParabolic
      ((starM X R (M ⊓ I)).subgroupOf (starImage X R X)) 3 (ZMod 2)) ∨
    (1 < F.degree ∧ IsLinearMaximalParabolic
      ((starM X R (M ⊓ I)).subgroupOf (starImage X R X)) 3 F.Carrier) := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  apply naturalThree_marked_parabolic h ?_ (selection.toSelected.not_chi hno) hCJ s F a hext
  exact (M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G)))

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue

namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

include hsource in
/-- Apply doubled-natural parabolic recognition to the original selected X, R and NI. -/
theorem normalized_component_doubleThree_parabolic
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (F : BinaryField)
    (ht : (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))) = ⊤)
    (a : ActionEquiv (s.space.toRepresentation.comp
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))).subtype)
        (repeated (linearNatural F 3) 2)) :
    let R := (M ⊓ I).pCoreIn 2
    (F.degree = 1 ∧ IsLinearMaximalParabolic
      ((starM X R (M ⊓ I)).subgroupOf (starImage X R X)) 3 (ZMod 2)) ∨
    (1 < F.degree ∧ IsLinearMaximalParabolic
      ((starM X R (M ⊓ I)).subgroupOf (starImage X R X)) 3 F.Carrier) := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  apply doubleThree_marked_parabolic h ?_ (selection.toSelected.not_chi hno) hCJ s F ht a
  exact (M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G)))

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
