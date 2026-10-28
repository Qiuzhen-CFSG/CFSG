/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayDistribution

/-!
Golay octads form the Steiner system S(5,8,24).
Minimum distance gives uniqueness through five points, and the 759-octad count
makes the incidence projection bijective, proving existence.

Source: `Atlas/Codes/WittDesign.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset

noncomputable def octads : Finset (Finset Omega) :=
  (univ.filter (fun w : golay => hammingNorm w.val = 8)).image (fun w => support w.val)

theorem support_injective : Function.Injective (support : BinaryWord → Finset Omega) :=
  binarySupportEquiv.injective

theorem octads_mem (O : Finset Omega) : O ∈ octads ↔
    ∃ w : golay, hammingNorm w.val = 8 ∧ support w.val = O := by
  classical
  simp only [octads, mem_image, mem_filter, mem_univ, true_and]

theorem octads_card : octads.card = 759 := by
  classical
  rw [octads, card_image_of_injective _ (fun _ _ h => Subtype.ext (support_injective h))]
  have h := golay_weight_distribution 8
  simpa [golayWeightCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem octad_size (O : Finset Omega) (hO : O ∈ octads) : O.card = 8 := by
  obtain ⟨w,hw,rfl⟩ := (octads_mem O).mp hO
  exact hw

theorem octad_unique_on_five (T O P : Finset Omega) (hT : T.card = 5)
    (hO : O ∈ octads) (hP : P ∈ octads) (hTO : T ⊆ O) (hTP : T ⊆ P) : O = P := by
  classical
  obtain ⟨u,hu,rfl⟩ := (octads_mem O).mp hO
  obtain ⟨v,hv,rfl⟩ := (octads_mem P).mp hP
  by_cases huv : u.val = v.val
  · rw [huv]
  have hn : u.val + v.val ≠ 0 := by
    intro hz
    apply huv
    funext i
    have hi := congrFun hz i
    have hh : ∀ x y : Bit, x + y = 0 → x = y := by decide
    exact hh _ _ hi
  have hm := golay_minimum _ (golay.add_mem u.prop v.prop) hn
  have he := binary_weight_add u.val v.val
  rw [hu,hv] at he
  have ht : 5 ≤ overlap u.val v.val := by
    rw [overlap_inter]
    rw [← hT]
    exact card_le_card (subset_inter hTO hTP)
  omega

abbrev Octad := {O : Finset Omega // O ∈ octads}
abbrev FiveSet := {T : Finset Omega // T.card = 5}
abbrev OctadIncidence := Σ O : Octad, {T : Finset Omega // T ∈ O.val.powersetCard 5}


def incidenceProjection (x : OctadIncidence) : FiveSet :=
  ⟨x.2.val, (mem_powersetCard.mp x.2.prop).2⟩

theorem incidenceProjection_injective : Function.Injective incidenceProjection := by
  rintro ⟨O,T⟩ ⟨P,U⟩ h
  have ht : T.val = U.val := congrArg Subtype.val h
  have hO : O = P := Subtype.ext (octad_unique_on_five T.val O.val P.val
    (mem_powersetCard.mp T.prop).2 O.prop P.prop
    (mem_powersetCard.mp T.prop).1 (ht ▸ (mem_powersetCard.mp U.prop).1))
  subst P
  have hT : T = U := Subtype.ext ht
  subst U
  rfl

theorem incidenceProjection_bijective : Function.Bijective incidenceProjection := by
  classical
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨incidenceProjection_injective, ?_⟩
  have hO : Fintype.card Octad = 759 := by
    rw [Fintype.card_subtype]
    simpa using octads_card
  have hf (O : Octad) : Fintype.card {T : Finset Omega // T ∈ O.val.powersetCard 5} = (8 : ℕ).choose 5 := by
    rw [Fintype.card_subtype]
    simp only [filter_mem_eq_inter, univ_inter, card_powersetCard, octad_size O.val O.prop]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  change Fintype.card (Σ O : Octad, {T : Finset Omega // T ∈ O.val.powersetCard 5}) =
    Fintype.card {T : Finset Omega // T.card = 5}
  rw [Fintype.card_sigma]
  simp only [hf, sum_const, smul_eq_mul, Fintype.card_finset_len]
  norm_num [Omega, HexIndex, Nat.choose, octads_card]

theorem octad_steiner (T : Finset Omega) (hT : T.card = 5) :
    ∃! O : Finset Omega, O ∈ octads ∧ T ⊆ O := by
  obtain ⟨⟨O,U⟩,he⟩ := incidenceProjection_bijective.2 (⟨T,hT⟩ : FiveSet)
  have hu : U.val = T := congrArg Subtype.val he
  refine ⟨O.val, ⟨O.prop, hu ▸ (mem_powersetCard.mp U.prop).1⟩, ?_⟩
  intro P hP
  exact octad_unique_on_five T P O.val hT hP.1 O.prop hP.2
    (hu ▸ (mem_powersetCard.mp U.prop).1)

end Atlas.Codes
