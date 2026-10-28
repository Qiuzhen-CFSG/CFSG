module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
public import Theory.SpecificGroups.BinaryLinear.QuinticNormalizerAutomorphisms
public import Theory.SpecificGroups.BinaryLinear.SixSectionCore
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# The binary-five exclusion with the original small normalizer index

Let B be a self-centralizing normal GL₅(2), A a perfect subgroup of B with
A/O₂(A) isomorphic to A₆, and R a nontrivial two-subgroup. Suppose A
normalizes R and N(R) normalizes A. If a Sylow of B meets N_B(A) in index
at most four, the two-core of A is nontrivial. Its quintic normalizer forces
N(A), and hence R, into B. Inside B, N_B(R) is an endpoint parabolic,
contains a full Sylow, and normalizes A. The already proved full-Sylow
A₆-section exclusion gives the contradiction.

This connects the intrinsic two-local geometry to the literal quotient
configuration in original 12.6.17; it assumes no full-Sylow normalization
of A at the outset. Source: Aschbacher--Smith, printed p.827, with
A.3.12(4--5), pp.47--48, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
open _root_.BinaryLinear BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private theorem section_local_of_normalizes (S : Sylow 2 G) (A : Subgroup G)
    [Group.IsPerfect A] (hS : (S : Subgroup G) ≤ normalizer (A : Set G))
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) :
    A ∈ localCComponents S := by
  let J := A ⊔ (S : Subgroup G)
  let A₀ := A.subgroupOf J
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hS)
  let a : A₀ ≃* A := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect A₀ := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (A₀ ⧸ pCore 2 A₀) := IsQuasisimple.of_mulEquiv b.symm
  have hp : IsPPerfect 2 A₀ := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (A₀ ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (A₀ ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (A₀ ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (A₀ ⧸ N) inferInstance
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : A₀.Normal).isSubnormal hp

theorem no_six_mutual_normalizer_five
    (A U : Subgroup (LinearGroup 5)) [Group.IsPerfect A]
    (eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (hU : IsPGroup 2 U) (hu : U ≠ ⊥)
    (hA : A ≤ normalizer (U : Set (LinearGroup 5)))
    (hN : normalizer (U : Set (LinearGroup 5)) ≤ normalizer (A : Set (LinearGroup 5))) : False := by
  have h5 : 5 ∣ Nat.card A := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 A))
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  obtain ⟨S,hS⟩ := QuinticNormalizer.exists_sylow_le_normalizer U hU hu
    (h5.trans (card_dvd_of_le hA))
  apply not_section_binary_linear S A (section_local_of_normalizes S A (hS.trans hN) eA)
    eA (Or.inr rfl)
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨(projectiveEquivLinear (by decide : 0 < 5)).symm⟩⟩
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
open _root_.BinaryLinear BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

theorem no_six_small_normalizer_five_socle
    (B A R : Subgroup G) [B.Normal] [Group.IsPerfect A]
    (eB : B ≃* LinearGroup 5) (hc : centralizer (B : Set G) = ⊥)
    (hAB : A ≤ B) (eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (hR : IsPGroup 2 R) (hr : R ≠ ⊥)
    (hAR : A ≤ normalizer (R : Set G))
    (hNR : normalizer (R : Set G) ≤ normalizer (A : Set G))
    (S : Sylow 2 B) (hi : (normalizer (A.subgroupOf B : Set B)).relIndex S ≤ 4) : False := by
  let A₀ := A.subgroupOf B
  let a : A₀ ≃* A := subgroupOfEquivOfLe hAB
  let A' := A₀.map eB.toMonoidHom
  let a' := A₀.equivMapOfInjective eB.toMonoidHom eB.injective
  let eA₀ := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eA
  let eA' := (QuotientGroup.congr _ _ a' (pCore_map_iso 2 a')).symm.trans eA₀
  let S' := S.mapSurjective (f := eB.toMonoidHom) eB.surjective
  have hi' : (normalizer (A' : Set (LinearGroup 5))).relIndex S' ≤ 4 := by
    change (normalizer (A₀.map eB.toMonoidHom : Set (LinearGroup 5))).relIndex ((S : Subgroup B).map eB.toMonoidHom) ≤ 4
    rw [←map_equiv_normalizer_eq,relIndex_map_map,
      (MonoidHom.ker_eq_bot_iff eB.toMonoidHom).mpr eB.injective,sup_bot_eq,sup_bot_eq]
    exact hi
  have hcore : pCore 2 A₀ ≠ ⊥ := by
    intro hz
    have hh := pCore_map_iso 2 a'
    rw [hz,Subgroup.map_bot] at hh
    exact QuinticNormalizer.six_section_core_ne_bot A' eA' S' hi' hh.symm
  let U := A₀.pCoreIn 2
  have hU : U ≠ ⊥ := fun hh => hcore ((map_eq_bot_iff_of_injective _ A₀.subtype_injective).mp hh)
  have h5 : 5 ∣ Nat.card A₀ := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 A₀))
    rw [Nat.card_congr eA₀.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hAn : A₀ ≤ normalizer (U : Set B) :=
    A₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A₀ (pCore 2 A₀))
  have hN : normalizer (U.map B.subtype : Set G) ≤ B :=
    QuinticNormalizer.normalizer_le_of_binaryFive_normal B eB hc U
      (isPGroup_pCoreIn 2 A₀) hU (h5.trans (card_dvd_of_le hAn))
  have hUeq : U.map B.subtype = A.pCoreIn 2 := by
    rw [show U = A₀.pCoreIn 2 from rfl,map_pCoreIn_of_injective 2 _ _ B.subtype_injective,
      map_subgroupOf_eq_of_le hAB]
  rw [hUeq] at hN
  have hNA : normalizer (A : Set G) ≤ B :=
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)).trans hN
  have hRB : R ≤ B := (R.le_normalizer.trans hNR).trans hNA
  let R₀ := R.subgroupOf B
  let R' := R₀.map eB.toMonoidHom
  have hR₀ : R₀ ≠ ⊥ := by
    intro hz
    have hh := congrArg (Subgroup.map B.subtype) hz
    rw [map_subgroupOf_eq_of_le hRB,Subgroup.map_bot] at hh
    exact hr hh
  have hAR₀ : A₀ ≤ normalizer (R₀ : Set B) := by
    rw [←subgroupOf_normalizer_eq hRB]
    exact comap_mono hAR
  have hNR₀ : normalizer (R₀ : Set B) ≤ normalizer (A₀ : Set B) := by
    rw [←subgroupOf_normalizer_eq hRB,←subgroupOf_normalizer_eq hAB]
    exact comap_mono hNR
  let : Group.IsPerfect A₀ := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect A' := Group.IsPerfect.map eB.toMonoidHom
  apply no_six_mutual_normalizer_five A' R' eA' (hR.comap_subtype.map _)
    (fun hh => hR₀ ((map_eq_bot_iff_of_injective _ eB.injective).mp hh))
  · exact (map_mono hAR₀).trans_eq (map_equiv_normalizer_eq R₀ eB)
  · change normalizer (R₀.map eB.toMonoidHom : Set (LinearGroup 5)) ≤ normalizer (A₀.map eB.toMonoidHom : Set (LinearGroup 5))
    rw [←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
    exact map_mono hNR₀
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
