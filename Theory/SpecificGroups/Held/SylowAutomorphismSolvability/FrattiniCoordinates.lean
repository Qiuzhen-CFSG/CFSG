module

public import Theory.GroupTheory.BinaryGraphQuotient
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Schreier

/-!
# Actual Frattini coordinates for the Held Sylow representative

The ten published PC words receive four binary coordinates. The checked
triangular conjugation relations and ten square identities also hold for
their graph generators. Binary graph collection and the proved order lower
bound construct an actual homomorphism to C₂⁴. Four displayed images give
surjectivity. The four original generators bound the elementary abelian
Frattini quotient by sixteen, so the map's kernel is exactly Φ(P).

The square identities are checked on the proved four-point base of Held.He;
all conjugation identities are reused from the original literal carrier.
This supplies quotient coordinates for the later automorphism-invariant
profile argument. It does not yet assert solvability of Aut(P) or Out(He).

Source: the ATLAS HeG1-p2058B0 and HeG1-max3W1 words and the certified
polycyclic data in LocalPairs/SylowGeometry/Calculations/TwoGroup/Source.
The intended source consumer is the A.3.9 full outer-solvability step.
-/

namespace Held.SylowAutomorphismSolvability.FrattiniCoordinates
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations
open Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
open Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables

public abbrev Representative := representative
public abbrev Coordinate := Multiplicative (Fin 4 → ZMod 2)

@[expose] public def pcElement (i : Fin 10) : Representative :=
  ⟨pcGenerator i, by
    have hm : pcGenerator i ∈ closure (Set.range pcGenerator) := subset_closure ⟨i, rfl⟩
    exact (congrArg (fun H : Subgroup Held.He => pcGenerator i ∈ H)
      pcClosure_eq_representative).mp hm⟩
@[expose] public def coordinateMask : Fin 10 → ℕ := ![0,8,8,8,8,8,4,4,2,1]
@[expose] public def coordinateGenerator (i : Fin 10) : Coordinate := Multiplicative.ofAdd
  (fun j => (coordinateMask i / 2 ^ j.val % 2 : ℕ))
private def sqWord (i : Fin 10) : List (Fin 10) := if i = 9 then [1,2] else []

private theorem square_check : ∀ (i : Fin 10) (k : Fin 4),
    (pcTable i ^ 2) ⟨k.val, by omega⟩ =
      ((sqWord i).map pcTable).prod ⟨k.val, by omega⟩ := by
  decide +kernel

private theorem square_actual (i : Fin 10) :
    pcGenerator i ^ 2 = ((sqWord i).map pcGenerator).prod := by
  apply Held.eq_of_four_point_images
  intro k
  simpa only [map_pow, map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq]
    using square_check i k

private theorem square_tag : ∀ i : Fin 10,
    coordinateGenerator i ^ 2 = ((sqWord i).map coordinateGenerator).prod := by decide +kernel
private theorem conjugate_tag : ∀ i j : Fin 10, j.val < i.val →
    coordinateGenerator i * coordinateGenerator j * (coordinateGenerator i)⁻¹ = ((conjugateWord i j).map coordinateGenerator).prod := by decide +kernel
private theorem square_support : ∀ i j : Fin 10, j ∈ sqWord i → j.val < i.val := by
  decide +kernel
private theorem conjugate_support : ∀ i j k : Fin 10,
    k ∈ conjugateWord i j → k.val < i.val := by decide +kernel

private theorem pair_prod (l : List (Fin 10)) :
    (l.map (fun j => (pcElement j, coordinateGenerator j))).prod = ((l.map pcElement).prod, (l.map coordinateGenerator).prod) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rfl

private theorem pair_square (i : Fin 10) :
    (pcElement i, coordinateGenerator i) ^ 2 ∈ generatorPrefix (fun j => (pcElement j, coordinateGenerator j)) i.val := by
  have he : (pcElement i, coordinateGenerator i) ^ 2 = ((sqWord i).map (fun j => (pcElement j, coordinateGenerator j))).prod := by
    rw [pair_prod]
    apply Prod.ext
    · apply Subtype.ext
      simpa [pcElement, Subgroup.val_list_prod, List.map_map, Function.comp_def] using square_actual i
    · exact square_tag i
  rw [he]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact (generatorPrefix_le _ _ _).mp le_rfl j (square_support i j hj)

private theorem pair_normalizes (i : Fin 10) :
    (pcElement i, coordinateGenerator i) ∈ normalizer
      (generatorPrefix (fun j => (pcElement j, coordinateGenerator j)) i.val : Set (Representative × Coordinate)) := by
  unfold generatorPrefix
  apply mem_normalizer_closure_of_conjugates
  rintro _ ⟨j, hj, rfl⟩
  have he : (pcElement i, coordinateGenerator i) * (pcElement j, coordinateGenerator j) * (pcElement i, coordinateGenerator i)⁻¹ =
      ((conjugateWord i j).map (fun k => (pcElement k, coordinateGenerator k))).prod := by
    rw [pair_prod]
    apply Prod.ext
    · apply Subtype.ext
      simpa [pcElement, Subgroup.val_list_prod, List.map_map, pcProduct, Function.comp_def] using
        pcGenerator_conjugate i j hj
    · exact conjugate_tag i j hj
  rw [he]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  exact subset_closure ⟨k, conjugate_support i j k hk, rfl⟩

private theorem generators_top : closure (Set.range pcElement) = ⊤ := by
  apply Subgroup.map_injective Representative.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Representative.range_subtype]
  rw [← Set.range_comp]
  change closure (Set.range pcGenerator) = representative
  exact pcClosure_eq_representative

public theorem exists_coordinate_hom : ∃ f : Representative →* Coordinate, ∀ i, f (pcElement i) = coordinateGenerator i := by
  exact Theory.GroupTheory.BinaryGraph.exists_hom_of_graph_collection pcElement coordinateGenerator generators_top
    (InnerNormalizer.representative_card_ge_of_orbit_labels InnerNormalizer.orbitSizeLabel_eq_card_orbit)
    pair_square pair_normalizes

end Held.SylowAutomorphismSolvability.FrattiniCoordinates

namespace Held.SylowAutomorphismSolvability.FrattiniCoordinates
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations
open scoped IsMulCommutative

private def r (i : Fin 4) : Representative := ⟨generator i, generator_mem i⟩
private theorem r_generates : closure (Set.range r) = ⊤ := by
  apply Subgroup.map_injective Representative.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Representative.range_subtype]
  rw [← Set.range_comp]
  change closure (Set.range generator) = representative
  rfl

private theorem rank_le_four : Group.rank Representative ≤ 4 := by
  classical
  let S : Finset Representative := Finset.univ.image r
  have hS : closure (S : Set Representative) = ⊤ := by
    simpa only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ] using r_generates
  exact (Group.rank_le hS).trans (by
    simpa using Finset.card_image_le (f := r) (s := Finset.univ))

private theorem vector_pow_two (v : Coordinate) : v ^ 2 = 1 := by
  have h : ∀ v : Coordinate, v ^ 2 = 1 := by decide +kernel
  exact h v

private instance : IsElementaryAbelian 2 Coordinate where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one vector_pow_two

private theorem vector_word : ∀ v : Coordinate,
    coordinateGenerator 9 ^ (v.toAdd 0).val * coordinateGenerator 8 ^ (v.toAdd 1).val *
      coordinateGenerator 6 ^ (v.toAdd 2).val * coordinateGenerator 1 ^ (v.toAdd 3).val = v := by
  decide +kernel

private theorem coordinate_surjective (f : Representative →* Coordinate) (hf : ∀ i, f (pcElement i) = coordinateGenerator i) :
    Function.Surjective f := by
  intro v
  refine ⟨pcElement 9 ^ (v.toAdd 0).val * pcElement 8 ^ (v.toAdd 1).val *
    pcElement 6 ^ (v.toAdd 2).val * pcElement 1 ^ (v.toAdd 3).val, ?_⟩
  simp only [map_mul, map_pow, hf]
  exact vector_word v

private theorem coordinate_kernel (f : Representative →* Coordinate) (hf : Function.Surjective f) :
    f.ker = frattini Representative := by
  let : Fact (IsPGroup 2 Representative) := ⟨representative_isPGroup⟩
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
    have hr : Group.rank (Representative ⧸ frattini Representative) ≤ 4 :=
      (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini Representative))
        (QuotientGroup.mk'_surjective _)).trans rank_le_four
    have hcard : Nat.card Coordinate = 16 := by simp [Coordinate, Nat.card_eq_fintype_card]
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

/-- The literal Held representative has the displayed elementary abelian
Frattini quotient, obtained from actual collection identities. -/
public theorem exists_frattini_coordinate :
    ∃ f : Representative →* Coordinate, Function.Surjective f ∧ f.ker = frattini Representative ∧
      ∀ i, f (pcElement i) = coordinateGenerator i := by
  obtain ⟨f, hf⟩ := exists_coordinate_hom
  have hs := coordinate_surjective f hf
  exact ⟨f, hs, coordinate_kernel f hs, hf⟩

end Held.SylowAutomorphismSolvability.FrattiniCoordinates
