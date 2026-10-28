module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Hyperplane
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Geometry
/-!
# Native octad moments and translation displacements

The sum of the sixteen exterior binary coordinates, weighted by a word,
vanishes on each of the twelve Golay generators. Descending this moment and
combining it with octad parity gives a surjection onto five binary dimensions,
whose kernel is precisely the supported octad pair space. The literal native
translations act by adding parity times their four-bit direction. Exterior
pair classes supply fixed representatives of every direction.

Source: Aschbacher--Smith, H.15.2(4--6), printed pp.398--399. Coordinates are
those already certified by `MathieuCode.SmallKernelFixed`.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open Representation.BinaryOffender
namespace MathieuCode.CocodeOctad.Dynamics
open SmallKernelFixed
noncomputable section

abbrev E := Fin 4 → ZMod 2

def moment : Full →ₗ[ZMod 2] E where
  toFun w := ∑ j : Fin 16, w (coordinate j) • decode j
  map_add' w v := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

lemma moment_row (r : Fin 12) : moment (row r) = 0 := by
  revert r
  decide +kernel

lemma golay_le_ker_moment : golay ≤ moment.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact moment_row r

def cocodeMoment : Cocode →ₗ[ZMod 2] E :=
  codeInCore.liftQ (moment.comp Core.subtype) (fun _ h => golay_le_ker_moment h)

lemma cocodeMoment_mk (w : Core) : cocodeMoment (codeInCore.mkQ w) = moment w.val := rfl

def coordinates : Cocode →ₗ[ZMod 2] (ZMod 2 × E) :=
  (octadParity seedOctad).prod cocodeMoment

lemma coordinate_injective : Function.Injective coordinate := by decide +kernel
lemma coordinate_not_mem (j : Fin 16) : coordinate j ∉ seedOctad.val := by
  simp only [mem_seedOctad]
  revert j
  decide +kernel
lemma coordinate_ne_zero (j : Fin 16) : coordinate j ≠ 0 := by revert j; decide +kernel
lemma decode_zero : decode 0 = 0 := by decide +kernel

lemma moment_single (i : Fin 24) :
    moment (Pi.single i 1) = ∑ j : Fin 16, if coordinate j = i then decode j else 0 := by
  simp [moment, Pi.single_apply, eq_comm]

lemma moment_coordinate (j : Fin 16) : moment (Pi.single (coordinate j) 1) = decode j := by
  simp only [moment_single, coordinate_injective.eq_iff]
  simp

lemma moment_octad (i : Fin 24) (hi : i ∈ seedOctad.val) :
    moment (Pi.single i 1) = 0 := by
  rw [moment_single]
  apply Finset.sum_eq_zero
  intro j _
  exact if_neg (fun h : coordinate j = i => coordinate_not_mem j (h.symm ▸ hi))

def evenPair (i j : Fin 24) : Core :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [BinaryPermutation.mem_core, Finset.sum_add_distrib]⟩
def pairClass (i j : Fin 24) : Cocode := codeInCore.mkQ (evenPair i j)

lemma zero_mem_seed : (0 : Fin 24) ∈ seedOctad.val :=
  (mem_seedOctad _).mpr (Or.inl rfl)

lemma dotForm_pair (w : Full) (i j : Fin 24) :
    dotForm w (Pi.single i 1 + Pi.single j 1) = w i + w j := by
  change w ⬝ᵥ (Pi.single i 1 + Pi.single j 1) = _
  rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]

lemma parity_pairClass (i j : Fin 24) :
    octadParity seedOctad (pairClass i j) =
      wordOfSet seedOctad.val i + wordOfSet seedOctad.val j := by
  rw [pairClass, octadParity_mk]
  exact dotForm_pair _ i j

lemma coordinates_mixed (j : Fin 16) : coordinates (pairClass 0 (coordinate j)) =
    (1, decode j) := by
  apply Prod.ext
  · change octadParity seedOctad (pairClass 0 (coordinate j)) = 1
    rw [parity_pairClass]
    simp only [wordOfSet, if_pos zero_mem_seed, if_neg (coordinate_not_mem j), add_zero]
  · change cocodeMoment (pairClass 0 (coordinate j)) = decode j
    rw [pairClass, cocodeMoment_mk]
    change moment (Pi.single 0 1 + Pi.single (coordinate j) 1) = decode j
    rw [map_add, moment_octad 0 zero_mem_seed,
      moment_coordinate, zero_add]

lemma coordinates_surjective : Function.Surjective coordinates := by
  rintro ⟨p, a⟩
  obtain ⟨j, rfl⟩ := decode_bijective.2 a
  refine ⟨pairClass 0 (coordinate j) + (p + 1) • pairClass 0 (coordinate 0), ?_⟩
  rw [map_add, map_smul, coordinates_mixed, coordinates_mixed, decode_zero]
  apply Prod.ext
  · change 1 + (p + 1) * 1 = p
    rw [mul_one, add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  · change decode j + (p + 1) • (0 : E) = decode j
    rw [smul_zero, add_zero]

lemma supported_le_ker : supportedPairSpace seedOctad.val ≤ coordinates.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨P, hP, rfl⟩
  apply Prod.ext
  · exact supportedPairSpace_le_octadHyperplane seedOctad
      (pairVector_mem_supportedPairSpace _ hP)
  · change moment (wordOfSet P.val) = 0
    change (∑ j : Fin 16, wordOfSet P.val (coordinate j) • decode j) = 0
    apply Finset.sum_eq_zero
    intro j _
    have hj : coordinate j ∉ P.val := fun h => coordinate_not_mem j (hP h)
    simp [wordOfSet, hj]

lemma coordinates_ker : coordinates.ker = supportedPairSpace seedOctad.val := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq supported_le_ker
  have h := coordinates.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr coordinates_surjective, finrank_top, finrank_cocode] at h
  have ht : Module.finrank (ZMod 2) (ZMod 2 × E) = 5 := by
    simp [Module.finrank_prod, E]
  rw [ht] at h
  rw [finrank_supportedPairSpace]
  omega


lemma xor_self (n j : Fin 16) : xorIndex n (xorIndex n j) = j := by
  revert n j
  decide +kernel

lemma xor_zero (n : Fin 16) : xorIndex n 0 = n := by revert n; decide +kernel
lemma xor_same (n : Fin 16) : xorIndex n n = 0 := by revert n; decide +kernel

def xorEquiv (n : Fin 16) : Fin 16 ≃ Fin 16 := { toFun := xorIndex n, invFun := xorIndex n, left_inv := xor_self n, right_inv := xor_self n }

lemma inverse_coordinate (n j : Fin 16) :
    (translation n)⁻¹ • coordinate j = coordinate (xorIndex n j) := by
  apply (MulAction.injective (translation n))
  change translation n • ((translation n)⁻¹ • coordinate j) = translation n • coordinate (xorIndex n j)
  rw [smul_inv_smul, translation_coordinate, xor_self]

lemma moment_action (n : Fin 16) (w : Full) :
    moment (fullRepresentation (translation n) w) =
      moment w + (∑ j : Fin 16, w (coordinate j)) • decode n := by
  change (∑ j : Fin 16, w ((translation n)⁻¹ • coordinate j) • decode j) = _
  simp only [inverse_coordinate]
  calc
    _ = ∑ j : Fin 16, w (coordinate j) • decode (xorIndex n j) := by
      apply Fintype.sum_equiv (xorEquiv n)
      intro j
      change _ = w (coordinate (xorIndex n j)) • decode (xorIndex n (xorIndex n j))
      rw [xor_self]
    _ = _ := by
      simp only [decode_xor, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
      exact add_comm _ _

lemma exterior_image : Finset.univ.image coordinate = seedOctad.valᶜ := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl]
  constructor
  · rintro ⟨j, rfl⟩
    exact coordinate_not_mem j
  · intro hi
    exact (coordinate_cover i).resolve_left hi

lemma parity_core (w : Core) :
    (∑ j : Fin 16, w.val (coordinate j)) = octadParity seedOctad (codeInCore.mkQ w) := by
  rw [octadParity_mk]
  have he : (∑ j : Fin 16, w.val (coordinate j)) = ∑ i ∈ seedOctad.valᶜ, w.val i := by
    rw [← exterior_image, Finset.sum_image]
    exact fun _ _ _ _ h => coordinate_injective h
  rw [he]
  have hs : (∑ i ∈ seedOctad.valᶜ, w.val i) + ∑ i ∈ seedOctad.val, w.val i = 0 := by
    rw [Finset.sum_compl_add_sum]
    exact w.property
  have hd : dotForm (wordOfSet seedOctad.val) w.val = ∑ i ∈ seedOctad.val, w.val i := by
    change (∑ i, (if i ∈ seedOctad.val then 1 else 0) * w.val i) = _
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hd]
  simpa only [ZMod.neg_eq_self_mod_two] using eq_neg_of_add_eq_zero_left hs

lemma translation_stabilizer (n : Fin 16) : translation n ∈ octadStabilizer seedOctad := by
  obtain ⟨g, _, he⟩ := translation_mem n
  exact he ▸ g.property

lemma coordinates_action (n : Fin 16) (v : Cocode) :
    coordinates (cocodeRepresentation (translation n) v) =
      ((coordinates v).1, (coordinates v).2 + (coordinates v).1 • decode n) := by
  apply Prod.ext
  · exact octadParity_invariant seedOctad ⟨translation n, translation_stabilizer n⟩ v
  · change cocodeMoment (cocodeRepresentation (translation n) v) =
      cocodeMoment v + octadParity seedOctad v • decode n
    obtain ⟨w, rfl⟩ := codeInCore.mkQ_surjective v
    rw [cocodeRepresentation_mk, cocodeMoment_mk, cocodeMoment_mk]
    exact (moment_action n w.val).trans (by rw [parity_core])

lemma full_single_action (g : M24) (i : Fin 24) :
    fullRepresentation g (Pi.single i 1) = Pi.single (g • i) 1 := by
  ext j
  change (Pi.single i (1 : ZMod 2) : Full) (g.val.symm j) =
    (Pi.single (g.val i) (1 : ZMod 2) : Full) j
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

lemma pairClass_action (g : M24) (i j : Fin 24) :
    cocodeRepresentation g (pairClass i j) = pairClass (g • i) (g • j) := by
  rw [pairClass, cocodeRepresentation_mk, pairClass]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  change fullRepresentation g (Pi.single i 1 + Pi.single j 1) = _
  rw [map_add, full_single_action, full_single_action]
  rfl

def direction (n : Fin 16) : Cocode := pairClass (coordinate 0) (coordinate n)

lemma coordinates_direction (n : Fin 16) : coordinates (direction n) = (0, decode n) := by
  apply Prod.ext
  · change octadParity seedOctad (pairClass (coordinate 0) (coordinate n)) = 0
    rw [parity_pairClass]
    simp only [wordOfSet, if_neg (coordinate_not_mem _), add_zero]
  · change cocodeMoment (pairClass (coordinate 0) (coordinate n)) = decode n
    rw [pairClass, cocodeMoment_mk]
    change moment (Pi.single (coordinate 0) 1 + Pi.single (coordinate n) 1) = _
    rw [map_add, moment_coordinate, moment_coordinate, decode_zero, zero_add]

lemma direction_fixed (n : Fin 16) :
    cocodeRepresentation (translation n) (direction n) = direction n := by
  rw [direction, pairClass_action, translation_coordinate, translation_coordinate, xor_zero, xor_same]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  exact add_comm _ _

lemma direction_not_mem (n : Fin 16) (hn : n ≠ 0) :
    direction n ∉ supportedPairSpace seedOctad.val := by
  intro hd
  rw [← coordinates_ker] at hd
  have h := congrArg Prod.snd ((LinearMap.mem_ker.mp hd).symm.trans (coordinates_direction n))
  apply hn
  apply decode_bijective.1
  exact h.symm.trans decode_zero.symm

end
end MathieuCode.CocodeOctad.Dynamics
