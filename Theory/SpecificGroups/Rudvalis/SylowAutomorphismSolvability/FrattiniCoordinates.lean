module

public import Theory.GroupTheory.BinaryGraphQuotient
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.NormalFormCoverage
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Schreier

/-!
# The actual rank-three Frattini quotient of the Rudvalis Sylow candidate

Attach binary masks 4, 2, 5, 5, 5, 5, 0, ..., 0 to the original fourteen
ATLAS words. Five-point checks certify their squares; the previously proved
conjugation rows certify collection in the graph. Reverse the sequence only
for the ascending-prefix graph theorem. The known order 2^14 makes the
first graph projection bijective, giving the actual coordinate homomorphism.

Eleven literal conjugation rows show that every abelian image is generated
by the first three generators. The coordinate images span C₂³, so the
Frattini quotient cardinal bound identifies the kernel with Φ(candidate).
No assertion about Aut(candidate) follows here without an intrinsic profile.

Source: the preserved RuG1-max4W1 words and left-action convention in
Model.SylowOvergroups.RadicalCoverage.Sylow.Candidate; square witnesses in
Sylow/source/witnesses.json are checked here, and conjugation identities
come from LocalOrder.Collection. The intended consumer is the full
outer-solvability step of Aschbacher–Smith, Proposition A.3.9.
-/

namespace Rudvalis.SylowAutomorphismSolvability.FrattiniCoordinates
open Subgroup
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

public abbrev Representative := candidate
public abbrev Coordinate := Multiplicative (Fin 3 → ZMod 2)

@[expose] public def pcElement (i : Fin 14) : Representative :=
  ⟨candidateGenerator i, subset_closure ⟨i, rfl⟩⟩
@[expose] public def coordinateMask : Fin 14 → ℕ := ![4,2,5,5,5,5,0,0,0,0,0,0,0,0]
@[expose] public def coordinateGenerator (i : Fin 14) : Coordinate := Multiplicative.ofAdd
  (fun j => (coordinateMask i / 2 ^ j.val % 2 : ℕ))
private def sqWord (i : Fin 14) : List (Fin 14) :=
  if i = 7 then [11] else if i = 9 ∨ i = 10 then [11,12,13] else []

private theorem square_check : ∀ (i : Fin 14) (k : Fin 5),
    (generatorMap i)^[2] (k.castLE (by decide)) =
      evalWord generatorMap (sqWord i) (k.castLE (by decide)) := by
  decide +kernel

private theorem square_actual (i : Fin 14) :
    candidateGenerator i ^ 2 = ((sqWord i).map candidateGenerator).prod := by
  apply Rudvalis.eq_of_smul_first_five
  intro k
  rw [generator_pow_smul, prod_smul candidateGenerator generatorMap generator_smul]
  exact square_check i k

private theorem square_tag : ∀ i : Fin 14,
    coordinateGenerator i ^ 2 = ((sqWord i).map coordinateGenerator).prod := by decide +kernel
private theorem conjugate_tag : ∀ i j : Fin 14, i < j →
    coordinateGenerator i * coordinateGenerator j * (coordinateGenerator i)⁻¹ =
      ((conjugateWord i j).map coordinateGenerator).prod := by decide +kernel
private theorem square_support : ∀ i j : Fin 14, j ∈ sqWord i → i.val < j.val := by
  decide +kernel

private theorem pair_prod (l : List (Fin 14)) :
    (l.map (fun j => (pcElement j, coordinateGenerator j))).prod =
      ((l.map pcElement).prod, (l.map coordinateGenerator).prod) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rfl

private theorem pair_square (i : Fin 14) :
    (pcElement i.rev, coordinateGenerator i.rev) ^ 2 ∈
      generatorPrefix (fun j => (pcElement j.rev, coordinateGenerator j.rev)) i.val := by
  have he : (pcElement i.rev, coordinateGenerator i.rev) ^ 2 =
      ((sqWord i.rev).map (fun j => (pcElement j, coordinateGenerator j))).prod := by
    rw [pair_prod]
    apply Prod.ext
    · apply Subtype.ext
      simpa [pcElement, Subgroup.val_list_prod, List.map_map, Function.comp_def] using square_actual i.rev
    · exact square_tag i.rev
  rw [he]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have h := square_support i.rev j hj
  have hmem := (generatorPrefix_le (fun j => (pcElement j.rev, coordinateGenerator j.rev)) i.val _).mp le_rfl j.rev (by simp only [Fin.val_rev] at *; omega)
  simpa only [Fin.rev_rev] using hmem

private theorem pair_normalizes (i : Fin 14) :
    (pcElement i.rev, coordinateGenerator i.rev) ∈ normalizer
      (generatorPrefix (fun j => (pcElement j.rev, coordinateGenerator j.rev)) i.val :
        Set (Representative × Coordinate)) := by
  unfold generatorPrefix
  apply mem_normalizer_closure_of_conjugates
  rintro _ ⟨j, hj, rfl⟩
  change j.val < i.val at hj
  have hij : i.rev < j.rev := by
    change i.rev.val < j.rev.val
    simp only [Fin.val_rev]
    omega
  have he : (pcElement i.rev, coordinateGenerator i.rev) *
      (pcElement j.rev, coordinateGenerator j.rev) * (pcElement i.rev, coordinateGenerator i.rev)⁻¹ =
      ((conjugateWord i.rev j.rev).map (fun k => (pcElement k, coordinateGenerator k))).prod := by
    rw [pair_prod]
    apply Prod.ext
    · apply Subtype.ext
      simpa [pcElement, Subgroup.val_list_prod, List.map_map, Function.comp_def] using
        generator_conjugate i.rev j.rev hij
    · exact conjugate_tag i.rev j.rev hij
  rw [he]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  have ht := conjugateWord_tail i.rev j.rev k hk
  exact subset_closure ⟨k.rev, by
    change k.rev.val < i.val
    simp only [Fin.val_rev] at *
    omega, by simp⟩

public theorem generators_top : closure (Set.range pcElement) = ⊤ := by
  apply Subgroup.map_injective Representative.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Representative.range_subtype]
  rw [← Set.range_comp]
  rfl

public theorem exists_coordinate_hom :
    ∃ f : Representative →* Coordinate, ∀ i, f (pcElement i) = coordinateGenerator i := by
  have hrev : closure (Set.range (fun i : Fin 14 => pcElement i.rev)) = ⊤ := by
    have he : Set.range (fun i : Fin 14 => pcElement i.rev) = Set.range pcElement := by
      ext x
      exact ⟨fun ⟨i, h⟩ => ⟨i.rev, h⟩, fun ⟨i, h⟩ => ⟨i.rev, by simpa using h⟩⟩
    rw [he, generators_top]
  obtain ⟨f, hf⟩ := Theory.GroupTheory.BinaryGraph.exists_hom_of_graph_collection
    (fun i : Fin 14 => pcElement i.rev) (fun i : Fin 14 => coordinateGenerator i.rev)
    hrev (by rw [candidate_card]; decide) pair_square pair_normalizes
  exact ⟨f, fun i => by simpa only [Fin.rev_rev] using hf i.rev⟩

private theorem abelian_collection {A : Type*} [CommGroup A] (x : Fin 14 → A)
    (row : ∀ i j : Fin 14, i < j → x j = ((conjugateWord i j).map x).prod) :
    (∀ i : Fin 14, 6 ≤ i.val → x i = 1) ∧
    (∀ i : Fin 14, 2 ≤ i.val → i.val < 6 → x i = x 2) := by
  have h11 : x 11 = 1 := by
    have h := row 6 7 (by decide)
    change x 7 = x 7 * (x 11 * (1)) at h
    simpa only [mul_one, one_mul, left_eq_mul] using h
  have h13 : x 13 = 1 := by
    have h := row 1 9 (by decide)
    change x 9 = x 9 * (x 13 * (1)) at h
    simpa only [mul_one, one_mul, left_eq_mul] using h
  have h12 : x 12 = 1 := by
    have h := row 2 12 (by decide)
    change x 12 = x 13 * (1) at h
    simpa only [mul_one, one_mul, left_eq_mul, h13] using h
  have h8 : x 8 = 1 := by
    have h := row 0 6 (by decide)
    change x 6 = x 6 * (x 8 * (1)) at h
    simpa only [mul_one, one_mul, left_eq_mul] using h
  have h6 : x 6 = 1 := by
    have h := row 2 4 (by decide)
    change x 4 = x 4 * (x 6 * (x 11 * (x 12 * (1)))) at h
    simpa only [mul_one, one_mul, left_eq_mul, h11, h12] using h
  have h7 : x 7 = 1 := by
    have h := row 0 1 (by decide)
    change x 1 = x 1 * (x 6 * (x 7 * (1))) at h
    simpa only [mul_one, one_mul, left_eq_mul, h6] using h
  have h10 : x 10 = 1 := by
    have h := row 2 10 (by decide)
    change x 10 = x 7 * (x 13 * (1)) at h
    simpa only [mul_one, one_mul, left_eq_mul, h7, h13] using h
  have h9 : x 9 = 1 := by
    have h := row 0 9 (by decide)
    change x 9 = x 10 * (1) at h
    simpa only [mul_one, one_mul, left_eq_mul, h10] using h
  have h3 : x 3 = x 2 := by
    have h := row 0 2 (by decide)
    change x 2 = x 3 * (x 7 * (x 8 * (x 9 * (x 11 * (x 13 * (1)))))) at h
    simpa only [mul_one, one_mul, left_eq_mul, h7, h8, h9, h11, h13] using h.symm
  have h5 : x 5 = x 2 := by
    have h := row 1 2 (by decide)
    change x 2 = x 5 * (x 7 * (x 10 * (x 13 * (1)))) at h
    simpa only [mul_one, one_mul, left_eq_mul, h7, h10, h13] using h.symm
  have h4 : x 4 = x 2 := by
    have h := row 0 4 (by decide)
    change x 4 = x 5 * (1) at h
    simpa only [mul_one, one_mul, left_eq_mul, h5] using h
  constructor
  · intro i hi
    fin_cases i <;> (try norm_num at hi) <;> assumption
  · intro i hi hj
    fin_cases i <;> (try norm_num at hi) <;> (try norm_num at hj) <;> first | assumption | rfl

private theorem abelian_images {A : Type*} [CommGroup A] (f : Representative →* A) :
    (∀ i : Fin 14, 6 ≤ i.val → f (pcElement i) = 1) ∧
    (∀ i : Fin 14, 2 ≤ i.val → i.val < 6 → f (pcElement i) = f (pcElement 2)) := by
  apply abelian_collection
  intro i j hij
  have he : pcElement i * pcElement j * (pcElement i)⁻¹ =
      ((conjugateWord i j).map pcElement).prod := by
    apply Subtype.ext
    simpa [pcElement, Subgroup.val_list_prod, List.map_map, Function.comp_def] using
      generator_conjugate i j hij
  have h := congrArg f he
  simpa only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def,
    mul_assoc, mul_mul_inv_cancel'_right] using h

open scoped IsMulCommutative

private theorem abelian_image_rank_le_three {A : Type*} [CommGroup A] [Finite A]
    (f : Representative →* A) (hf : Function.Surjective f) : Group.rank A ≤ 3 := by
  classical
  let r : Fin 3 → A := fun i => f (pcElement (i.castLE (by decide)))
  have hfull := congrArg (fun H : Subgroup Representative => H.map f) generators_top
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hf] at hfull
  have hgen : closure (Set.range r) = ⊤ := by
    apply top_unique
    rw [← hfull]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨hzero, heq⟩ := abelian_images f
    by_cases h6 : 6 ≤ i.val
    · change f (pcElement i) ∈ _
      rw [hzero i h6]
      exact one_mem _
    · by_cases h2 : 2 ≤ i.val
      · change f (pcElement i) ∈ _
        rw [heq i h2 (by omega)]
        exact subset_closure ⟨2, rfl⟩
      · exact subset_closure ⟨⟨i.val, by omega⟩, rfl⟩
  let S : Finset A := Finset.univ.image r
  have hS : closure (S : Set A) = ⊤ := by
    simpa only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen
  exact (Group.rank_le hS).trans (by
    simpa using Finset.card_image_le (f := r) (s := Finset.univ))

private theorem vector_pow_two (v : Coordinate) : v ^ 2 = 1 := by
  have h : ∀ v : Coordinate, v ^ 2 = 1 := by decide +kernel
  exact h v

private instance : IsElementaryAbelian 2 Coordinate where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one vector_pow_two

private theorem vector_word : ∀ v : Coordinate,
    (coordinateGenerator 0 * coordinateGenerator 2) ^ (v.toAdd 0).val *
      coordinateGenerator 1 ^ (v.toAdd 1).val * coordinateGenerator 0 ^ (v.toAdd 2).val = v := by
  decide +kernel

public theorem coordinate_surjective (f : Representative →* Coordinate)
    (hf : ∀ i, f (pcElement i) = coordinateGenerator i) : Function.Surjective f := by
  intro v
  refine ⟨(pcElement 0 * pcElement 2) ^ (v.toAdd 0).val *
    pcElement 1 ^ (v.toAdd 1).val * pcElement 0 ^ (v.toAdd 2).val, ?_⟩
  simp only [map_mul, map_pow, hf]
  exact vector_word v

public theorem coordinate_kernel (f : Representative →* Coordinate) (hf : Function.Surjective f) :
    f.ker = frattini Representative := by
  let : Fact (IsPGroup 2 Representative) := ⟨candidate_isTwoGroup⟩
  let : IsElementaryAbelian 2 (Representative ⧸ frattini Representative) := isElementaryAbelian_quotient_frattini
  have hφ : frattini Representative ≤ f.ker := by
    let : Fact (IsPGroup 2 Coordinate) := ⟨IsElementaryAbelian.isPGroup 2 Coordinate⟩
    have h := frattini_le_comap_frattini_of_surjective hf
    simpa only [frattini_eq_bot_of_isElementaryAbelian (p := 2),
      MonoidHom.comap_bot] using h
  have hbound : Nat.card (Representative ⧸ frattini Representative) ≤ Nat.card Coordinate := by
    have hd := card_dvd_exponent_pow_rank' (Representative ⧸ frattini Representative)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Representative ⧸ frattini Representative)))
    have hr : Group.rank (Representative ⧸ frattini Representative) ≤ 3 :=
      abelian_image_rank_le_three (QuotientGroup.mk' (frattini Representative))
        (QuotientGroup.mk'_surjective _)
    have hcard : Nat.card Coordinate = 8 := by simp [Coordinate, Nat.card_eq_fintype_card]
    rw [hcard]
    exact (Nat.le_of_dvd (by positivity) hd).trans
      (by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr)
  let fbar : (Representative ⧸ frattini Representative) →* Coordinate := QuotientGroup.lift (frattini Representative) f hφ
  have hsurj : Function.Surjective fbar := by
    intro v
    obtain ⟨x, rfl⟩ := hf v
    exact ⟨QuotientGroup.mk' (frattini Representative) x, rfl⟩
  have hinj := (hsurj.bijective_of_nat_card_le hbound).1
  apply le_antisymm _ hφ
  intro x hx
  apply (QuotientGroup.eq_one_iff (N := frattini Representative) x).mp
  apply hinj
  change f x = fbar 1
  rw [map_one]
  exact hx

/-- The original fourteen-word candidate has the indicated rank-three
Frattini quotient, with the literal images of all fourteen generators. -/
public theorem exists_frattini_coordinate :
    ∃ f : Representative →* Coordinate, Function.Surjective f ∧ f.ker = frattini Representative ∧
      ∀ i, f (pcElement i) = coordinateGenerator i := by
  obtain ⟨f, hf⟩ := exists_coordinate_hom
  have hs := coordinate_surjective f hf
  exact ⟨f, hs, coordinate_kernel f hs, hf⟩

end Rudvalis.SylowAutomorphismSolvability.FrattiniCoordinates
