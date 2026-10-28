module

public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow

/-!
# Normal four-groups in a native M23 Sylow subgroup

The certified Sylow enumeration has thirty-two involutions outside the common
four-group. For each of them, four distinct Sylow conjugates are displayed.
Together with the identity they would give five elements of any normal subgroup
containing that involution. Thus an elementary normal subgroup of order four is
contained in, and hence equals, the common four-group.

The finite checks use the actual native permutations from `Involutions.Fusion`;
there is no inference from the separate classification of E16 subgroups. Checks
are split by involution to bound kernel memory. The adjacent discovery script
only suggests the tables; every identity is proved in Lean.

Source: Aschbacher--Smith, the sporadic inspection in 15.3.43, printed p.1140,
combined manuscript of 1 March 2004; GLS3 Table 5.3d.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.FourNormalizers
open FusionCertificate ElementarySylow
set_option maxRecDepth 100000
set_option Elab.async false

private def outsideIndex : Fin 32 → Fin 128 := ![1, 3, 5, 6, 7, 8, 16, 17, 25, 34, 35, 42, 48, 50, 52, 53, 54, 59, 68, 75, 76, 85, 88, 91, 94, 102, 104, 107, 109, 119, 120, 127]

private def conjugatorIndex (k : Fin 32) : Fin 4 → Fin 128 :=
(#[
  ![0, 2, 8, 10],
  ![0, 1, 8, 9],
  ![0, 8, 16, 24],
  ![0, 1, 8, 9],
  ![0, 2, 8, 10],
  ![0, 1, 2, 3],
  ![0, 2, 3, 5],
  ![0, 2, 3, 5],
  ![0, 1, 2, 3],
  ![0, 2, 3, 5],
  ![0, 2, 3, 5],
  ![0, 1, 2, 3],
  ![0, 1, 8, 9],
  ![0, 2, 8, 10],
  ![0, 2, 8, 10],
  ![0, 1, 8, 9],
  ![0, 8, 16, 24],
  ![0, 1, 2, 3],
  ![0, 1, 2, 3],
  ![0, 1, 2, 4],
  ![0, 1, 2, 4],
  ![0, 1, 2, 3],
  ![0, 1, 8, 9],
  ![0, 1, 8, 9],
  ![0, 1, 8, 9],
  ![0, 1, 2, 3],
  ![0, 1, 8, 9],
  ![0, 1, 8, 9],
  ![0, 1, 8, 9],
  ![0, 1, 2, 3],
  ![0, 1, 2, 4],
  ![0, 1, 2, 4]
] : Array (Fin 4 → Fin 128))[k.val]'(k.isLt)

private def conjugateIndex (k : Fin 32) : Fin 4 → Fin 128 :=
(#[
  ![1, 7, 16, 120],
  ![3, 6, 48, 104],
  ![5, 88, 54, 107],
  ![6, 3, 104, 48],
  ![7, 1, 120, 16],
  ![8, 25, 42, 59],
  ![16, 75, 120, 35],
  ![17, 76, 127, 34],
  ![25, 8, 102, 68],
  ![34, 127, 76, 17],
  ![35, 120, 75, 16],
  ![42, 59, 85, 119],
  ![48, 53, 3, 91],
  ![50, 52, 35, 75],
  ![52, 50, 75, 35],
  ![53, 48, 91, 3],
  ![54, 107, 5, 88],
  ![59, 42, 25, 8],
  ![68, 102, 8, 25],
  ![75, 120, 35, 16],
  ![76, 127, 34, 17],
  ![85, 119, 68, 102],
  ![88, 107, 5, 54],
  ![91, 109, 53, 94],
  ![94, 104, 109, 6],
  ![102, 68, 119, 85],
  ![104, 94, 6, 109],
  ![107, 88, 54, 5],
  ![109, 91, 94, 53],
  ![119, 85, 59, 42],
  ![120, 75, 16, 35],
  ![127, 76, 17, 34]
] : Array (Fin 4 → Fin 128))[k.val]'(k.isLt)

private theorem candidate_coverage : ∀ (b : Fin 2) (j : Fin 16),
    (∃ a, candidateIndex b j = commonIndex a) ∨
      ∃ k, candidateIndex b j = outsideIndex k := by decide +kernel

private theorem exceptional_coverage : ∀ j : Fin 8,
    ∃ k, exceptionalIndex j = outsideIndex k := by decide +kernel

private theorem square_coverage (i : Fin 128) (hs : ∀ x, pointTable i (pointTable i x) = x) :
    (∃ j, i = commonIndex j) ∨ ∃ k, i = outsideIndex k := by
  rcases square_cases i hs with ⟨b, j, rfl⟩ | ⟨k, rfl⟩
  · exact candidate_coverage b j
  · exact Or.inr (exceptional_coverage k)

private theorem conjugation_points_0 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 0 j) (pointTable (outsideIndex 0) x) =
      pointTable (conjugateIndex 0 j) (pointTable (conjugatorIndex 0 j) x) := by
  decide +kernel

private theorem conjugation_points_1 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 1 j) (pointTable (outsideIndex 1) x) =
      pointTable (conjugateIndex 1 j) (pointTable (conjugatorIndex 1 j) x) := by
  decide +kernel

private theorem conjugation_points_2 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 2 j) (pointTable (outsideIndex 2) x) =
      pointTable (conjugateIndex 2 j) (pointTable (conjugatorIndex 2 j) x) := by
  decide +kernel

private theorem conjugation_points_3 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 3 j) (pointTable (outsideIndex 3) x) =
      pointTable (conjugateIndex 3 j) (pointTable (conjugatorIndex 3 j) x) := by
  decide +kernel

private theorem conjugation_points_4 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 4 j) (pointTable (outsideIndex 4) x) =
      pointTable (conjugateIndex 4 j) (pointTable (conjugatorIndex 4 j) x) := by
  decide +kernel

private theorem conjugation_points_5 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 5 j) (pointTable (outsideIndex 5) x) =
      pointTable (conjugateIndex 5 j) (pointTable (conjugatorIndex 5 j) x) := by
  decide +kernel

private theorem conjugation_points_6 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 6 j) (pointTable (outsideIndex 6) x) =
      pointTable (conjugateIndex 6 j) (pointTable (conjugatorIndex 6 j) x) := by
  decide +kernel

private theorem conjugation_points_7 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 7 j) (pointTable (outsideIndex 7) x) =
      pointTable (conjugateIndex 7 j) (pointTable (conjugatorIndex 7 j) x) := by
  decide +kernel

private theorem conjugation_points_8 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 8 j) (pointTable (outsideIndex 8) x) =
      pointTable (conjugateIndex 8 j) (pointTable (conjugatorIndex 8 j) x) := by
  decide +kernel

private theorem conjugation_points_9 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 9 j) (pointTable (outsideIndex 9) x) =
      pointTable (conjugateIndex 9 j) (pointTable (conjugatorIndex 9 j) x) := by
  decide +kernel

private theorem conjugation_points_10 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 10 j) (pointTable (outsideIndex 10) x) =
      pointTable (conjugateIndex 10 j) (pointTable (conjugatorIndex 10 j) x) := by
  decide +kernel

private theorem conjugation_points_11 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 11 j) (pointTable (outsideIndex 11) x) =
      pointTable (conjugateIndex 11 j) (pointTable (conjugatorIndex 11 j) x) := by
  decide +kernel

private theorem conjugation_points_12 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 12 j) (pointTable (outsideIndex 12) x) =
      pointTable (conjugateIndex 12 j) (pointTable (conjugatorIndex 12 j) x) := by
  decide +kernel

private theorem conjugation_points_13 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 13 j) (pointTable (outsideIndex 13) x) =
      pointTable (conjugateIndex 13 j) (pointTable (conjugatorIndex 13 j) x) := by
  decide +kernel

private theorem conjugation_points_14 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 14 j) (pointTable (outsideIndex 14) x) =
      pointTable (conjugateIndex 14 j) (pointTable (conjugatorIndex 14 j) x) := by
  decide +kernel

private theorem conjugation_points_15 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 15 j) (pointTable (outsideIndex 15) x) =
      pointTable (conjugateIndex 15 j) (pointTable (conjugatorIndex 15 j) x) := by
  decide +kernel

private theorem conjugation_points_16 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 16 j) (pointTable (outsideIndex 16) x) =
      pointTable (conjugateIndex 16 j) (pointTable (conjugatorIndex 16 j) x) := by
  decide +kernel

private theorem conjugation_points_17 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 17 j) (pointTable (outsideIndex 17) x) =
      pointTable (conjugateIndex 17 j) (pointTable (conjugatorIndex 17 j) x) := by
  decide +kernel

private theorem conjugation_points_18 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 18 j) (pointTable (outsideIndex 18) x) =
      pointTable (conjugateIndex 18 j) (pointTable (conjugatorIndex 18 j) x) := by
  decide +kernel

private theorem conjugation_points_19 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 19 j) (pointTable (outsideIndex 19) x) =
      pointTable (conjugateIndex 19 j) (pointTable (conjugatorIndex 19 j) x) := by
  decide +kernel

private theorem conjugation_points_20 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 20 j) (pointTable (outsideIndex 20) x) =
      pointTable (conjugateIndex 20 j) (pointTable (conjugatorIndex 20 j) x) := by
  decide +kernel

private theorem conjugation_points_21 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 21 j) (pointTable (outsideIndex 21) x) =
      pointTable (conjugateIndex 21 j) (pointTable (conjugatorIndex 21 j) x) := by
  decide +kernel

private theorem conjugation_points_22 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 22 j) (pointTable (outsideIndex 22) x) =
      pointTable (conjugateIndex 22 j) (pointTable (conjugatorIndex 22 j) x) := by
  decide +kernel

private theorem conjugation_points_23 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 23 j) (pointTable (outsideIndex 23) x) =
      pointTable (conjugateIndex 23 j) (pointTable (conjugatorIndex 23 j) x) := by
  decide +kernel

private theorem conjugation_points_24 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 24 j) (pointTable (outsideIndex 24) x) =
      pointTable (conjugateIndex 24 j) (pointTable (conjugatorIndex 24 j) x) := by
  decide +kernel

private theorem conjugation_points_25 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 25 j) (pointTable (outsideIndex 25) x) =
      pointTable (conjugateIndex 25 j) (pointTable (conjugatorIndex 25 j) x) := by
  decide +kernel

private theorem conjugation_points_26 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 26 j) (pointTable (outsideIndex 26) x) =
      pointTable (conjugateIndex 26 j) (pointTable (conjugatorIndex 26 j) x) := by
  decide +kernel

private theorem conjugation_points_27 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 27 j) (pointTable (outsideIndex 27) x) =
      pointTable (conjugateIndex 27 j) (pointTable (conjugatorIndex 27 j) x) := by
  decide +kernel

private theorem conjugation_points_28 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 28 j) (pointTable (outsideIndex 28) x) =
      pointTable (conjugateIndex 28 j) (pointTable (conjugatorIndex 28 j) x) := by
  decide +kernel

private theorem conjugation_points_29 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 29 j) (pointTable (outsideIndex 29) x) =
      pointTable (conjugateIndex 29 j) (pointTable (conjugatorIndex 29 j) x) := by
  decide +kernel

private theorem conjugation_points_30 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 30 j) (pointTable (outsideIndex 30) x) =
      pointTable (conjugateIndex 30 j) (pointTable (conjugatorIndex 30 j) x) := by
  decide +kernel

private theorem conjugation_points_31 : ∀ (j : Fin 4) (x : Fin 23),
    pointTable (conjugatorIndex 31 j) (pointTable (outsideIndex 31) x) =
      pointTable (conjugateIndex 31 j) (pointTable (conjugatorIndex 31 j) x) := by
  decide +kernel

private theorem conjugation_points (k : Fin 32) (j : Fin 4) (x : Fin 23) :
    pointTable (conjugatorIndex k j) (pointTable (outsideIndex k) x) =
      pointTable (conjugateIndex k j) (pointTable (conjugatorIndex k j) x) := by
  fin_cases k
  · exact conjugation_points_0 j x
  · exact conjugation_points_1 j x
  · exact conjugation_points_2 j x
  · exact conjugation_points_3 j x
  · exact conjugation_points_4 j x
  · exact conjugation_points_5 j x
  · exact conjugation_points_6 j x
  · exact conjugation_points_7 j x
  · exact conjugation_points_8 j x
  · exact conjugation_points_9 j x
  · exact conjugation_points_10 j x
  · exact conjugation_points_11 j x
  · exact conjugation_points_12 j x
  · exact conjugation_points_13 j x
  · exact conjugation_points_14 j x
  · exact conjugation_points_15 j x
  · exact conjugation_points_16 j x
  · exact conjugation_points_17 j x
  · exact conjugation_points_18 j x
  · exact conjugation_points_19 j x
  · exact conjugation_points_20 j x
  · exact conjugation_points_21 j x
  · exact conjugation_points_22 j x
  · exact conjugation_points_23 j x
  · exact conjugation_points_24 j x
  · exact conjugation_points_25 j x
  · exact conjugation_points_26 j x
  · exact conjugation_points_27 j x
  · exact conjugation_points_28 j x
  · exact conjugation_points_29 j x
  · exact conjugation_points_30 j x
  · exact conjugation_points_31 j x

private def fiveIndex (k : Fin 32) : Fin 5 → Fin 128 := Fin.cases 0 (conjugateIndex k)

private theorem fiveIndex_injective : ∀ k, Function.Injective (fiveIndex k) := by
  decide +kernel

private theorem conjugation_correct (k : Fin 32) (j : Fin 4) :
    perm (conjugatorIndex k j) * perm (outsideIndex k) *
      (perm (conjugatorIndex k j))⁻¹ = perm (conjugateIndex k j) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  exact Equiv.ext (conjugation_points k j)

private noncomputable def element (i : Fin 128) : M23 :=
  ⟨perm i, rawSubgroup_le (perm_mem i)⟩

private theorem element_mem (i : Fin 128) : element i ∈ subgroup := perm_mem i

private theorem outside_card_bound (V : Subgroup M23)
    (hNV : subgroup ≤ normalizer (V : Set M23)) (k : Fin 32)
    (hV : element (outsideIndex k) ∈ V) : 5 ≤ Nat.card V := by
  let f : Fin 5 → V := Fin.cases 1 (fun j =>
    ⟨element (conjugatorIndex k j) * element (outsideIndex k) *
      (element (conjugatorIndex k j))⁻¹,
      (mem_normalizer_iff.mp (hNV (element_mem _)) _).mp hV⟩)
  have hf (i : Fin 5) : (f i).val.val = perm (fiveIndex k i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact initial.symm
    · exact conjugation_correct k j
  have hinj : Function.Injective f := by
    intro i j hij
    apply fiveIndex_injective k
    apply perm_injective
    rw [← hf i, ← hf j, hij]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hinj

/-- The normal four-groups, unlike the order-sixteen elementary subgroups,
are determined by their Sylow conjugacy orbits. -/
theorem normal_four_eq_common (V : Subgroup M23) (hVS : V ≤ subgroup)
    (hSV : subgroup ≤ normalizer (V : Set M23))
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) : V = common := by
  apply Subgroup.eq_of_le_of_card_ge (K := common) ?_ (by rw [hc, common_card])
  intro v hv
  obtain ⟨i, hi⟩ := exists_perm ⟨v.val, hVS hv⟩
  have hs : ∀ x, pointTable i (pointTable i x) = x := by
    let _ := hV
    have he := congrArg (fun z : M23 => z.val)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv)
    rw [pow_two] at he
    change v.val * v.val = 1 at he
    rw [← hi] at he
    exact fun x => Equiv.congr_fun he x
  rcases square_coverage i hs with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · exact (mem_common v).mpr ⟨j, hi⟩
  · have hv' : element (outsideIndex k) ∈ V := (Subtype.ext hi : element _ = v) ▸ hv
    have hb := outside_card_bound V hSV k hv'
    omega

end Sporadic.Mathieu.M23Geometry.FourNormalizers
