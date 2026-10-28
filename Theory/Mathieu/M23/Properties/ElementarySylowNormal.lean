module
public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow
/-!
# Sylow normalization of order-sixteen elementary subgroups in M23

The three certified Sylow generators normalize both elementary candidates.
Checked permutation identities prove this without an ambient subgroup catalogue;
the existing elementary coverage and Sylow conjugacy then give the intrinsic
statement for every Sylow subgroup. This excludes a graph-swapping PSL3(4)
actor in the marked containing-component row of Aschbacher--Smith 14.2.9.
Source: Aschbacher--Smith H.14.2(1), printed p.397, and 14.2.9, p.983.
-/
public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M23Geometry.ElementarySylow
open FusionCertificate
private def conjugateIndex (b : Fin 2) (g : Fin 6) (i : Fin 16) : Fin 16 :=
  (![![![0, 11, 13, 6, 14, 5, 3, 8, 7, 12, 10, 1, 9, 2, 4, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 3, 2, 1, 6, 5, 4, 7, 13, 14, 15, 12, 11, 8, 9, 10],
    ![0, 11, 13, 6, 14, 5, 3, 8, 7, 12, 10, 1, 9, 2, 4, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 3, 2, 1, 6, 5, 4, 7, 13, 14, 15, 12, 11, 8, 9, 10]],
  ![![0, 10, 4, 14, 2, 8, 6, 12, 5, 15, 1, 11, 7, 13, 3, 9],
    ![0, 7, 15, 8, 9, 14, 6, 1, 3, 4, 12, 11, 10, 13, 5, 2],
    ![0, 3, 2, 1, 4, 7, 6, 5, 12, 15, 14, 13, 8, 11, 10, 9],
    ![0, 10, 4, 14, 2, 8, 6, 12, 5, 15, 1, 11, 7, 13, 3, 9],
    ![0, 7, 15, 8, 9, 14, 6, 1, 3, 4, 12, 11, 10, 13, 5, 2],
    ![0, 3, 2, 1, 4, 7, 6, 5, 12, 15, 14, 13, 8, 11, 10, 9]]] b) g i
private theorem gen_points_0_0 : ∀ (i : Fin 16) (x : Fin 23),
    gen 0 (perm (candidateIndex 0 i) x) =
      perm (candidateIndex 0 (conjugateIndex 0 0 i)) (gen 0 x) := by
  decide +kernel
private theorem gen_points_0_1 : ∀ (i : Fin 16) (x : Fin 23),
    gen 1 (perm (candidateIndex 0 i) x) =
      perm (candidateIndex 0 (conjugateIndex 0 1 i)) (gen 1 x) := by
  decide +kernel
private theorem gen_points_0_2 : ∀ (i : Fin 16) (x : Fin 23),
    gen 2 (perm (candidateIndex 0 i) x) =
      perm (candidateIndex 0 (conjugateIndex 0 2 i)) (gen 2 x) := by
  decide +kernel
private theorem gen_points_0_3 : ∀ (i : Fin 16) (x : Fin 23),
    gen 3 (perm (candidateIndex 0 i) x) =
      perm (candidateIndex 0 (conjugateIndex 0 3 i)) (gen 3 x) := by
  decide +kernel
private theorem gen_points_0_4 : ∀ (i : Fin 16) (x : Fin 23),
    gen 4 (perm (candidateIndex 0 i) x) =
      perm (candidateIndex 0 (conjugateIndex 0 4 i)) (gen 4 x) := by
  decide +kernel
private theorem gen_points_0_5 : ∀ (i : Fin 16) (x : Fin 23),
    gen 5 (perm (candidateIndex 0 i) x) =
      perm (candidateIndex 0 (conjugateIndex 0 5 i)) (gen 5 x) := by
  decide +kernel
private theorem gen_points_1_0 : ∀ (i : Fin 16) (x : Fin 23),
    gen 0 (perm (candidateIndex 1 i) x) =
      perm (candidateIndex 1 (conjugateIndex 1 0 i)) (gen 0 x) := by
  decide +kernel
private theorem gen_points_1_1 : ∀ (i : Fin 16) (x : Fin 23),
    gen 1 (perm (candidateIndex 1 i) x) =
      perm (candidateIndex 1 (conjugateIndex 1 1 i)) (gen 1 x) := by
  decide +kernel
private theorem gen_points_1_2 : ∀ (i : Fin 16) (x : Fin 23),
    gen 2 (perm (candidateIndex 1 i) x) =
      perm (candidateIndex 1 (conjugateIndex 1 2 i)) (gen 2 x) := by
  decide +kernel
private theorem gen_points_1_3 : ∀ (i : Fin 16) (x : Fin 23),
    gen 3 (perm (candidateIndex 1 i) x) =
      perm (candidateIndex 1 (conjugateIndex 1 3 i)) (gen 3 x) := by
  decide +kernel
private theorem gen_points_1_4 : ∀ (i : Fin 16) (x : Fin 23),
    gen 4 (perm (candidateIndex 1 i) x) =
      perm (candidateIndex 1 (conjugateIndex 1 4 i)) (gen 4 x) := by
  decide +kernel
private theorem gen_points_1_5 : ∀ (i : Fin 16) (x : Fin 23),
    gen 5 (perm (candidateIndex 1 i) x) =
      perm (candidateIndex 1 (conjugateIndex 1 5 i)) (gen 5 x) := by
  decide +kernel
private theorem gen_points (b : Fin 2) (g : Fin 6) (i : Fin 16) (x : Fin 23) :
    gen g (perm (candidateIndex b i) x) =
      perm (candidateIndex b (conjugateIndex b g i)) (gen g x) := by
  fin_cases b <;> fin_cases g
  · exact gen_points_0_0 i x
  · exact gen_points_0_1 i x
  · exact gen_points_0_2 i x
  · exact gen_points_0_3 i x
  · exact gen_points_0_4 i x
  · exact gen_points_0_5 i x
  · exact gen_points_1_0 i x
  · exact gen_points_1_1 i x
  · exact gen_points_1_2 i x
  · exact gen_points_1_3 i x
  · exact gen_points_1_4 i x
  · exact gen_points_1_5 i x
private theorem gen_normalizes (b : Fin 2) (g : Fin 6) :
    gen g ∈ normalizer (rawCandidate b : Set (Equiv.Perm (Fin 23))) := by
  have forward (g : Fin 6) (h : Equiv.Perm (Fin 23)) (hh : h ∈ rawCandidate b) :
      gen g * h * (gen g)⁻¹ ∈ rawCandidate b := by
    obtain ⟨i,rfl⟩ := hh
    refine ⟨conjugateIndex b g i, ?_⟩
    apply (eq_mul_inv_iff_mul_eq).mpr
    apply Equiv.ext
    intro x
    exact (gen_points b g i x).symm
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact forward g h
  · intro hh
    have hi := forward (invOf g) _ hh
    simpa only [gen_inv, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hi

theorem rawCandidate_normalized (b : Fin 2) :
    rawSubgroup ≤ normalizer (rawCandidate b : Set (Equiv.Perm (Fin 23))) := by
  rintro h ⟨w,rfl⟩
  induction w with
  | nil => exact (normalizer _).one_mem
  | cons i w ih => exact (normalizer _).mul_mem (gen_normalizes b i) ih

theorem candidate_normalized (b : Fin 2) :
    subgroup ≤ normalizer (candidate b : Set M23) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  exact mem_normalizer_iff.mp (rawCandidate_normalized b hg) h.val

theorem card16_normalized_in_sylow (P : Sylow 2 M23) (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (hAP : A ≤ (P : Subgroup M23)) :
    (P : Subgroup M23) ≤ normalizer (A : Set M23) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 P sylow
  let e := MulAut.conj g
  have hP : (P : Subgroup M23).map e.toMonoidHom = subgroup := by
    have hh : (P : Subgroup M23).map e.toMonoidHom =
        (sylow : Subgroup M23) := congrArg Sylow.toSubgroup hg
    simpa only [sylow, Sylow.coe_ofCard] using hh
  obtain ⟨b,hb⟩ := card16_eq_candidate (A.map e.toMonoidHom)
    (by let := hA; exact IsElementaryAbelian.map _)
    ((card_map_of_injective e.injective).trans hcard) (hP ▸ map_mono hAP)
  have h := candidate_normalized b
  rw [←hb, ←hP, ←map_equiv_normalizer_eq] at h
  exact (map_le_map_iff_of_injective e.injective).mp h
end Sporadic.Mathieu.M23Geometry.ElementarySylow
