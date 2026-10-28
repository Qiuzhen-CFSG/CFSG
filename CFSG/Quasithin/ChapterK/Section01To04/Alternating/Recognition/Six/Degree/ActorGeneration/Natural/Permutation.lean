module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Contracts
public import Theory.Alternating.TripleSixActorGeneration
public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget.Transport
import Mathlib.Tactic.FinCases


/-!
# The literal permutation action in the natural A₆ generation calculation

The injective S₆ action preserves the elementary actor and its binary rank.
Conjugation commutes with this action, so permutation generation gives the
required inner automorphism containment. An even involution supplies three
A₆ conjugates by the checked intrinsic A₆ generation theorem. The sign map
provides such an involution whenever the elementary actor has order at least four.

Source: the group-generation bound used for Aschbacher–Smith K.1.1, printed
p.452 / PDF p.463, citing GM02 Theorem 6.2 and Table 6.3. This is an intrinsic
generation calculation, not the full representation-theoretic conclusion.
-/

@[expose] public section

open scoped IsMulCommutative
open Equiv Subgroup Representation.BinaryOffender AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
abbrev S6 := Perm (Fin 6)

theorem three_of_even (E : Subgroup S6) (t : A6)
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) (htE : (t : S6) ∈ E) :
    ∃ c : Fin 3 → A6, alternatingGroup (Fin 6) ≤
      ⨆ i, E.map (MulAut.conj (c i : S6)).toMonoidHom := by
  obtain ⟨g, h, hgen⟩ := alternatingGroup.TripleSixActorGeneration.three_conjugates_generate t ht ht2
  let c : Fin 3 → A6 := ![1, g, h]
  let H : Subgroup S6 := ⨆ i, E.map (MulAut.conj (c i : S6)).toMonoidHom
  have hm (i : Fin 3) : ((c i * t * (c i)⁻¹ : A6) : S6) ∈ H :=
    (le_iSup (fun i => E.map (MulAut.conj (c i : S6)).toMonoidHom) i)
      (mem_map_of_mem _ htE)
  have hsub : (⊤ : Subgroup A6) ≤ H.comap (alternatingGroup (Fin 6)).subtype := by
    rw [← hgen]
    apply sup_le
    · apply sup_le
      · apply zpowers_le.mpr
        change (t : S6) ∈ H
        simpa [c] using hm 0
      · exact zpowers_le.mpr (hm 1)
    · exact zpowers_le.mpr (hm 2)
  exact ⟨c, fun x hx => hsub (show (⟨x,hx⟩ : A6) ∈ (⊤ : Subgroup A6) from mem_top _)⟩

theorem exists_even_of_card_gt_two (E : Subgroup S6) (hcard : 2 < Nat.card E) :
    ∃ t : A6, t ≠ 1 ∧ (t : S6) ∈ E := by
  classical
  by_contra! hn
  let f : E →* ℤˣ := Perm.sign.comp E.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    have he : (x : S6) ∈ alternatingGroup (Fin 6) := hx
    have hx1 : (⟨(x : S6), he⟩ : A6) = 1 := by
      by_contra h
      exact hn ⟨x,he⟩ h x.property
    change x = 1
    apply Subtype.ext
    exact congrArg (fun a : A6 => (a : S6)) hx1
  have hc := Nat.card_le_card_of_injective f hf
  have htwo : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
  omega

theorem permutation_span_to_natural (E : Subgroup S6) {n : ℕ} (c : Fin n → A6)
    (hc : alternatingGroup (Fin 6) ≤ ⨆ i, E.map (MulAut.conj (c i : S6)).toMonoidHom) :
    AlternatingSix.ShadowLocal.inner ≤
      ⨆ i, (E.map permutationAction).map (MulAut.conj (MulAut.conj (c i))).toMonoidHom := by
  have hm (i : Fin n) :
      (E.map (MulAut.conj (c i : S6)).toMonoidHom).map permutationAction =
      (E.map permutationAction).map (MulAut.conj (MulAut.conj (c i))).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
  rintro _ ⟨x, rfl⟩
  have hx := mem_map_of_mem permutationAction (hc x.property)
  rw [Subgroup.map_iSup] at hx
  simp only [hm, permutationAction_coe] at hx
  exact hx

theorem preimage_elementary (A : Subgroup AutA6) (hA : IsElementaryTwo A) (hAn : A ≤ natural) :
    IsElementaryTwo (A.comap permutationAction) ∧
      (A.comap permutationAction).map permutationAction = A ∧
      rank (A.comap permutationAction) = rank A := by
  let E := A.comap permutationAction
  have he : E.map permutationAction = A := Subgroup.map_comap_eq_self hAn
  let : IsElementaryAbelian 2 A := hA.2
  have elem : IsElementaryAbelian 2 E := {
    toIsMulCommutative := ⟨⟨fun x y => by
      apply Subtype.ext
      apply permutationAction_injective
      change permutationAction ((x : S6) * y) = permutationAction ((y : S6) * x)
      simpa only [map_mul, Subgroup.coe_mul] using congrArg (fun a : A => (a : AutA6))
        (mul_comm (⟨permutationAction x,x.property⟩ : A) ⟨permutationAction y,y.property⟩)⟩⟩
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      apply permutationAction_injective
      change permutationAction ((x : S6) ^ 2) = permutationAction 1
      simpa only [map_pow, map_one] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (permutationAction (x : S6)) x.property }
  refine ⟨⟨?_, elem⟩, he, ?_⟩
  · intro hb
    apply hA.1
    change E = ⊥ at hb
    rw [← he, hb, Subgroup.map_bot]
  · have hc := Subgroup.card_map_of_injective (K := E) permutationAction_injective
    rw [he] at hc
    exact congrArg (Nat.log 2) hc.symm

end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
