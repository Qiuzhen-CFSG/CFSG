module

public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport

/-!
# Two Hermitian pairs adapted to an isotropic plane

A basis of a totally isotropic plane has dual partners because its perpendicular
has codimension two. Trace surjectivity adjusts the partners to norm one;
subtracting a multiple of the first isotropic vector makes the pairs orthogonal.
The result is the four-dimensional part of the adapted basis used in the
unitary-five instance of Witt extension (GLS3 Lemma 2.7.1, printed p.89,
`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public noncomputable section

open Matrix Module BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive.IsotropicGeometry
namespace Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.PlaneBasis
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

lemma pair_add_left (u v w : Fin 5 → F) :
    pairing J (u + v) w = pairing J u w + pairing J v w := by
  simp only [pairing, Pi.add_apply, map_add, ← Pi.add_def, add_dotProduct]
lemma pair_add_right (u v w : Fin 5 → F) :
    pairing J u (v + w) = pairing J u v + pairing J u w := by
  exact dotProduct_add _ _ _
lemma pair_smul_left (a : F) (v w : Fin 5 → F) :
    pairing J (a • v) w = J.conj a * pairing J v w := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, map_mul]
  exact smul_dotProduct (J.conj a) (fun i => J.conj (v i)) w
lemma pair_smul_right (a : F) (v w : Fin 5 → F) :
    pairing J v (a • w) = a * pairing J v w := by
  exact dotProduct_smul _ _ _
@[simp] lemma pair_zero_left (w : Fin 5 → F) : pairing J 0 w = 0 := by simp [pairing]
@[simp] lemma pair_zero_right (w : Fin 5 → F) : pairing J w 0 = 0 := by simp [pairing]
lemma pair_conj (v w : Fin 5 → F) : J.conj (pairing J v w) = pairing J w v := by
  simp only [pairing, dotProduct, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [J.conj_involutive]
  exact mul_comm _ _
lemma pair_self_fixed (v : Fin 5 → F) : J.conj (pairing J v v) = pairing J v v :=
  pair_conj J v v
lemma pair_nondegenerate (v : Fin 5 → F) (h : ∀ w, pairing J w v = 0) : v = 0 := by
  ext i
  have hi := h (Pi.single i 1)
  simpa [pairing, dotProduct, Pi.single_apply, apply_ite] using hi

noncomputable def pairMap (v : Fin 5 → F) : (Fin 5 → F) →ₗ[F] F where
  toFun := pairing J v
  map_add' := pair_add_right J v
  map_smul' a w := pair_smul_right J a v w

lemma pair_sum_left {ι : Type*} (s : Finset ι) (v : ι → Fin 5 → F) (w : Fin 5 → F) :
    pairing J (∑ i ∈ s, v i) w = ∑ i ∈ s, pairing J (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, pair_add_left, ih]

lemma exists_dual_partners [Finite F] (W : Submodule F (Fin 5 → F))
    (hd : Module.finrank F W = 2) :
    ∃ (e : Basis (Fin 2) F W) (f : Fin 2 → Fin 5 → F),
      ∀ i j, pairing J (e i) (f j) = if i = j then 1 else 0 := by
  classical
  let e := Module.finBasisOfFinrankEq F W hd
  let T : (Fin 5 → F) →ₗ[F] (Fin 2 → F) := LinearMap.pi fun i => pairMap J (e i)
  have hk : LinearMap.ker T = orthogonal J W := by
    ext v
    rw [LinearMap.mem_ker, funext_iff]
    change (∀ i, pairing J (e i) v = 0) ↔ ∀ w ∈ W, pairing J w v = 0
    constructor
    · intro hv w hw
      have he := congrArg (fun x : W => pairing J x.val v) (e.sum_repr ⟨w, hw⟩)
      rw [← he]
      simp only [Submodule.coe_sum, Submodule.coe_smul, pair_sum_left, pair_smul_left, hv,
        mul_zero, Finset.sum_const_zero]
    · intro hv i
      exact hv _ (e i).property
  have hr : LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_iff_finrank_eq.mpr
    have hh := T.finrank_range_add_finrank_ker
    rw [hk, finrank_orthogonal, hd] at hh
    simp only [Module.finrank_pi, Fintype.card_fin] at hh ⊢
    omega
  have ht := LinearMap.range_eq_top.mp hr
  choose f hf using fun j : Fin 2 => ht (Pi.single j 1)
  refine ⟨e, f, ?_⟩
  intro i j
  have hh := congrFun (hf j) i
  simpa only [T, LinearMap.pi_apply, pairMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, eq_comm] using hh

def gramFour : Matrix (Fin 4) (Fin 4) F :=
  !![0,1,0,0; 1,1,0,0; 0,0,0,1; 0,0,1,1]

lemma pair_reverse {v w : Fin 5 → F} {a : F} (h : pairing J v w = a) :
    pairing J w v = J.conj a := by rw [← pair_conj, h]

lemma exists_plane_frame [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (W : Submodule F (Fin 5 → F)) (hd : Module.finrank F W = 2)
    (hi : W ≤ orthogonal J W) :
    ∃ (e : Basis (Fin 2) F W) (v : Fin 4 → Fin 5 → F),
      v 0 = e 0 ∧ v 2 = e 1 ∧ ∀ i j, pairing J (v i) (v j) = gramFour i j := by
  classical
  obtain ⟨e, f, hf⟩ := exists_dual_partners J W hd
  have he (i j : Fin 2) : pairing J (e i) (e j) = 0 := hi (e j).property _ (e i).property
  have hfe (i j : Fin 2) : pairing J (f i) (e j) = if i = j then 1 else 0 := by
    rw [pair_reverse J (hf j i)]
    split_ifs <;> simp_all
  have adjust (i : Fin 2) : ∃ g : Fin 5 → F,
      pairing J g g = 1 ∧ ∀ j, pairing J (e j) g = if j = i then 1 else 0 := by
    obtain ⟨a, ha⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
      hcard (fixed_card_four J hcard hconj) (1 - pairing J (f i) (f i))
      (by rw [map_sub, map_one, pair_self_fixed])
    refine ⟨f i + a • (e i).val, ?_, ?_⟩
    · simp only [pair_add_left, pair_add_right, pair_smul_left, pair_smul_right,
        hf, hfe, he, ite_true, mul_one, mul_zero, add_zero]
      linear_combination ha
    · intro j
      simp only [pair_add_right, pair_smul_right, he, mul_zero, add_zero, hf]
  obtain ⟨u, huu, heu⟩ := adjust 0
  obtain ⟨w, hww, hew⟩ := adjust 1
  have hue (j : Fin 2) : pairing J u (e j) = if j = 0 then 1 else 0 := by
    rw [pair_reverse J (heu j)]
    split_ifs <;> simp
  have hwe (j : Fin 2) : pairing J w (e j) = if j = 1 then 1 else 0 := by
    rw [pair_reverse J (hew j)]
    split_ifs <;> simp
  let z := w + (-pairing J u w) • (e 0).val
  have huz : pairing J u z = 0 := by
    simp only [z, pair_add_right, pair_smul_right, hue, ite_true, mul_one, add_neg_cancel]
  have hez (j : Fin 2) : pairing J (e j) z = if j = 1 then 1 else 0 := by
    simp only [z, pair_add_right, pair_smul_right, he, hew, mul_zero, add_zero]
  have hzz : pairing J z z = 1 := by
    simp only [z, pair_add_left, pair_add_right, pair_smul_left, pair_smul_right,
      hwe, hew, he, hww]
    norm_num
  have hzu : pairing J z u = 0 := by simpa using pair_reverse J huz
  have hze (j : Fin 2) : pairing J z (e j) = if j = 1 then 1 else 0 := by
    rw [pair_reverse J (hez j)]
    split_ifs <;> simp
  refine ⟨e, ![(e 0).val, u, (e 1).val, z], rfl, rfl, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gramFour, he, heu, hue, hez, hze, huu, hzz, huz, hzu]

end Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.PlaneBasis
