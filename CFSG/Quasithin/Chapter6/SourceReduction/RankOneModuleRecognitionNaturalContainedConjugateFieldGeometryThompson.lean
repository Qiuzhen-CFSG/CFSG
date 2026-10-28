module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModelRecognition
public import Theory.SpecificGroups.PSL2.RootInvolutionFixedCard
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Stellmacher.MaxElementaryOffender
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Thompson control for the involutory field fixed space

A full natural Sylow cannot preserve the field-fixed plane: the field
involution fixes only the square root of its order. The natural-offender
classification therefore excludes offenders in the plane normalizer.
Elementary replacement turns any moving maximal elementary subgroup into
an offender, proving J(S) = J(C_S(B)).

Source: Aschbacher–Smith, 6.1.14(1), printed pp.670–671. These are the
Thompson equalities used to promote the arranged relative Sylow subgroup.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}

/-- The field-fixed plane is never normalized by an entire Sylow of L. -/
theorem field_fixedSpace_not_normalized_by_sylow
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (P : Sylow 2 L) :
    ¬ (P : Subgroup L).map L.subtype ≤ normalizer (U : Set G) := by
  intro hP
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, _, htB, hU, K, _, _, _, _, a, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, haout⟩ := field_quotientActor e a t σ hσ hσsq hσact
  have hi : Function.Involutive (vectorActor f ⟨t, htB⟩) := by
    apply intertwiner_involutive_of_fixed (quotientActor e t) _
      (vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    have hu := u.property
    let v : B := ⟨u, (hU.le hu).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le hu).2
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  let S := P.mapSurjective hq
  have hfix (s : S) : quotientActor e t (s : Matrix.SpecialLinearGroup (Fin 2) F) = s := by
    obtain ⟨l, hl, heq⟩ := s.property
    rw [← heq]
    exact (mem_normalizer_fixed_iff e f hf t htB hU hi hasq haout l).mp
      (hP (mem_map_of_mem L.subtype hl))
  have hnorm : (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map
      (quotientActor e t).toMonoidHom = S := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      change quotientActor e t s ∈ S
      rw [hfix ⟨s, hs⟩]
      exact hs
    · intro s hs
      exact ⟨s, hs, hfix ⟨s, hs⟩⟩
  have hc := Theory.PSL2.RootSemilinear.sylow_fixed_card_sq_of_equiv
    (Theory.PSL2.sl2QuotientEquiv F) S (quotientActor e t) hnorm hasq haout
  let ef : {s : S // quotientActor e t (s : Matrix.SpecialLinearGroup (Fin 2) F) = s} ≃ S :=
    { toFun := Subtype.val
      invFun s := ⟨s, hfix s⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr ef] at hc
  have hs : Nat.card S = Nat.card F :=
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have hF : 1 < Nat.card F := Finite.one_lt_card
  rw [hs] at hc
  nlinarith

variable [IsElementaryAbelian 2 B]
open Representation.BinaryOffender
/-- A natural offender cannot preserve the field-fixed plane. -/
theorem field_fixedSpace_no_offender_normalizer
    (hn : 2 ≤ n) (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (A : Subgroup G)
    (hAU : A ≤ normalizer (U : Set G)) :
    ¬ IsOffender (ChapterE.automizerRepresentation B) (ChapterE.inducedAutomizer B A) := by
  intro hA
  obtain ⟨P, hP⟩ := NaturalAction.offender_lifts_sylow hn hnatural hNL hA
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  have hUB : U ≤ B := by
    obtain ⟨_, _, _, hU, _⟩ := hfield
    exact hU.le.trans inf_le_left
  apply field_fixedSpace_not_normalized_by_sylow hnatural hfield hUne P
  rintro p ⟨l, hl, rfl⟩
  have him : B.normalizerMonoidHom.rangeRestrict ⟨(l : G), hLB l.property⟩ ∈
      ChapterE.inducedAutomizer B A := by
    rw [hP]
    exact ⟨_, mem_map_of_mem L.subtype hl, rfl⟩
  obtain ⟨a, ha, he⟩ := him
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨u, hu, rfl⟩
    have hh := congrArg (fun x : ChapterE.Automizer B => (x.val ⟨u, hUB hu⟩ : G)) he
    change (a : G) * u * (a : G)⁻¹ = (l : G) * u * (l : G)⁻¹ at hh
    change (l : G) * u * (l : G)⁻¹ ∈ U
    rw [← hh]
    exact (mem_normalizer_iff.mp (hAU ha) u).mp hu
  · rw [card_map_of_injective (MulAut.conj (l : G)).injective]
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem card_inf_mul_relIndex (H K : Subgroup G) :
    Nat.card (H ⊓ K : Subgroup G) * H.relIndex K = Nat.card K := by
  simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ K) K bot_le inf_le_right

/-- A maximum elementary subgroup acting nontrivially on a normal elementary
subgroup gives an offender in the literal ambient automizer. -/
theorem maxElementary_induced_offender (S B A : Subgroup G)
    [IsElementaryAbelian 2 B] (hBS : B ≤ S)
    (hSN : S ≤ normalizer (B : Set G))
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hne : ¬ A ≤ centralizer (B : Set G)) :
    IsOffender (ChapterE.automizerRepresentation B) (ChapterE.inducedAutomizer B A) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hAN := hA.1.trans hSN
  refine ⟨⟨fun he => hne ((ChapterE.inducedAutomizer_eq_bot_iff hAN).mp he),
    ChapterE.inducedAutomizer_elementary B A hAN⟩, ?_⟩
  rw [ChapterE.fixedCodim_inducedAutomizer B A hAN,
    ChapterE.rank_inducedAutomizer B A hAN]
  apply Nat.log_mono_right
  let C := A ⊓ centralizer (B : Set G)
  let F := B ⊓ centralizer (A : Set G)
  let I := B ⊓ C
  have hCA : C ≤ A := inf_le_left
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCA
  have hsup : IsElementaryAbelian 2 (B ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (show C ≤ centralizer (B : Set G) from inf_le_right)
  have hmax := hA.2.2 (B ⊔ C) (sup_le hBS (hCA.trans hA.1)) hsup
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hIC : Nat.card I ≤ Nat.card F := card_le_of_le (le_inf inf_le_left
    ((inf_le_right.trans hCA).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)))
  have hCAcard : Nat.card C * C.relIndex A = Nat.card A := by
    simpa only [inf_of_le_left hCA] using card_inf_mul_relIndex C A
  have hFBcard : Nat.card F * F.relIndex B = Nat.card B := by
    simpa only [inf_of_le_left (show F ≤ B from inf_le_left)] using card_inf_mul_relIndex F B
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hFpos : 0 < Nat.card F := Nat.card_pos
  change F.relIndex B ≤ C.relIndex A
  have h1 : Nat.card B * Nat.card C ≤ Nat.card I * Nat.card A := by
    rw [hprod]
    exact Nat.mul_le_mul_left _ hmax
  have h2 : Nat.card B ≤ Nat.card I * C.relIndex A := by
    nlinarith [hCAcard]
  nlinarith [Nat.mul_le_mul_right (C.relIndex A) hIC]

/-- Every maximum elementary subgroup of a subgroup preserving the field
plane acts trivially on the whole natural module. Consequently its Thompson
subgroup agrees with that of its module centralizer. -/
theorem field_fixedSpace_thompson_centralizes
    {L M B U : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 B]
    (hn : 2 ≤ n) (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (S : Subgroup G) (hBS : B ≤ S)
    (hSB : S ≤ normalizer (B : Set G)) (hSU : S ≤ normalizer (U : Set G)) :
    (∀ A ∈ elementaryAbelianMaxSubgroups S, A ≤ centralizer (B : Set G)) ∧
      elementaryAbelianMaxJ S = elementaryAbelianMaxJ (S ⊓ centralizer (B : Set G)) := by
  have hmax (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups S) :
      A ≤ centralizer (B : Set G) := by
    by_contra hnA
    exact field_fixedSpace_no_offender_normalizer hn hnatural hNL hfield hUne A
      (hA.1.trans hSU) (maxElementary_induced_offender S B A hBS hSB hA hnA)
  refine ⟨hmax, ?_⟩
  symm
  apply elementaryAbelianMaxJ_eq_of_intermediate_finite S _ _ inf_le_left
  exact sSup_le fun A hA => le_inf hA.1 (hmax A hA)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
