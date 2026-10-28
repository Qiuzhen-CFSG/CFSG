module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.TwoQuotient
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.Quasithin.Rank

/-!
# Normality forced by a large proper local component

The four nonnormal C-component models in original 1.2.1(3) cannot contain
the actual local block occurring in the moved alternating-five argument.
The binary rank-one models have no proper full-Sylow local C-component.
The odd linear models and J1 have no elementary two-subgroup of order sixteen.

The final consumer restricts the actual full Sylow and contained block to an
ordinary component. Its central two-core quotient retains the block marking
and elementary sixteen. The full known-simple 1.2.1 source theorem then forces
normality. No invariant-single-block hypothesis is imposed.

Source: Aschbacher--Smith 14.6.9, printed p.1026; 1.2.1(3), p.504,
and A.3.12, pp.47--48.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
open ChapterA.Section03 Chapter1.Section02 ChapterC
open SourceEmbeddings.FiveLocalFF

/-- A proper full-Sylow local component and an elementary sixteen exclude
every actual nonnormal C-component model. -/
theorem not_nonnormal_model
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (E : Subgroup A)
    (hE : IsElementaryAbelian 2 E) (hcard : 16 ≤ Nat.card E) :
    ¬ NonnormalCComponentModel A := by
  intro hm
  cases hm with
  | linear_even n hn he =>
      exact CarrierSieve.not_bender_model S B hB hproper (.linear n hn he)
  | suzuki m hm he =>
      exact CarrierSieve.not_bender_model S B hB hproper (.suzuki m hm he)
  | linear_prime p hp ho he =>
      exact CarrierSieve.not_odd_model E hE hcard
        (.linear_two p 1 hp ho (by decide) (by simpa only [pow_one] using he))
  | janko he =>
      exact SporadicSieve.not_jankoOne E hE hcard he.some

/-- The literal ordinary component is normal once its two-core quotient
contains the proper full-Sylow local block and its elementary sixteen. -/
theorem ordinary_component_normal_of_large_proper_local
    {X : Type*} [Group X] [Finite X]
    (hQ : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X))
    (A : Subgroup X) (hA : IsComponent X A)
    (S : Sylow 2 (A ⧸ pCore 2 A)) (B : Subgroup (A ⧸ pCore 2 A))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (E : Subgroup (A ⧸ pCore 2 A)) (hE : IsElementaryAbelian 2 E)
    (hcard : 16 ≤ Nat.card E) : A.Normal := by
  let : IsQuasisimple A := hA.2
  have hsize : 1 < Nat.card (A ⧸ pCore 2 A) :=
    lt_of_lt_of_le (by omega : 1 < Nat.card E) E.card_le_card_group
  let : Nontrivial (A ⧸ pCore 2 A) := Finite.one_lt_card_iff_nontrivial.mp hsize
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' (pCore 2 A))
      (QuotientGroup.mk'_surjective _)
  rcases proposition_1_2_1_three_index_knownSimple hQ hA.isCComponent with hn | ⟨_, hm⟩
  · exact hn
  · exact (not_nonnormal_model S B hB hproper E hE hcard hm).elim

/-- An ordinary component containing the actual local alternating-five block is normal.
The quotient block and elementary sixteen are constructed from the original marking. -/
theorem ordinary_component_normal_of_contained_alternating_five
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (B : Subgroup X) (hB : B ∈ localCComponents S)
    (hb : IsAlternatingBlock B 5)
    (A : Subgroup X) (hA : IsComponent X A) (hBA : B ≤ A) : A.Normal := by
  let : IsQuasisimple A := hA.2
  obtain ⟨SA, _, hlocal⟩ := SourceEmbeddings.exists_local_sylow_restriction S hB hBA hA.1
  let C := B.subgroupOf A
  have hC : IsAlternatingBlock C 5 := hb.of_mulEquiv (subgroupOfEquivOfLe hBA).symm
  let q := QuotientGroup.mk' (pCore 2 A)
  let D := C.map q
  have hker : (q.subgroupMap C).ker = (pCore 2 A).comap C.subtype := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    rfl
  have hkp : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [hker]
    exact pCore_isPGroup.comap_subtype
  have hkc : (q.subgroupMap C).ker ≤ center C := by
    rw [hker]
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (mem_center_iff.mp (IsQuasisimple.pCore_le_center 2 hx)) y
  have hD : IsAlternatingBlock D 5 := hC.of_surjective_central_two_kernel
    (q.subgroupMap C) (q.subgroupMap_surjective C) hkp hkc
  have hproper : D ≠ ⊤ := by
    intro he
    have ht := hD.of_mulEquiv ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv)
    exact ht.2.1.core_ne_bot (pCore_quotient_pCore_eq_bot 2)
  let E := (blockU D).map D.subtype
  have he : IsElementaryAbelian 2 E := hD.2.1.elementary.map D.subtype
  have hc : Nat.card E = 16 :=
    (card_map_of_injective D.subtype_injective).trans hD.blockU_card
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := A)
    infer_instance
  have hQ : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_, hX.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hX.stronglyQuasithin p hp ho)
  exact ordinary_component_normal_of_large_proper_local hQ A hA
    (SA.mapSurjective (QuotientGroup.mk'_surjective _)) D
    (localCComponents_map_of_solvable_ker hlocal q) hproper E he hc.ge

end CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
