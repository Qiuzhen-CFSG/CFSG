module
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.SpecificGroups.BinaryLinear.ElementaryOuterSylowReduction

/-!
# The binary graph-Sylow degree obstruction

Conjugate the actual Sylow subgroup to the upper unitriangular group. The
reversing matrix turns inverse transpose into an automorphism of that group;
the remaining inner adjustment belongs to its normalizer, hence is itself
unitriangular over the binary field. Inner adjustment fixes the first
superdiagonal, so graph displacements have the sum of an edge and its reversal.

In degree three the first displacement has a nonzero square entry. In every
degree at least five the first two displacements fail to commute, detected on
the second superdiagonal. Thus an elementary graph-Sylow displacement action
has degree four. This statement deliberately retains that exceptional degree.
The final theorem applies it to the original outer action through its actual
full-linear equivalence, discharging the premise of the earlier reduction.

Source: Aschbacher--Smith G.10.15(3), printed p.363 of `refs/quasithin.pdf`.
-/

public noncomputable section

open Matrix
namespace BinaryLinear.ElementaryOuterSylow

private theorem upper_mul_gap_one {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (dA : ∀ i, A i i = 1) (dB : ∀ i, B i i = 1)
    (i j : Fin n) (hij : j.val = i.val + 1) :
    (A * B) i j = B i j + A i j := by
  have ij : i ≠ j := by intro h; subst j; omega
  have hs : (∑ l ∈ ({i,j} : Finset (Fin n)), A i l * B l j) =
      ∑ l, A i l * B l j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    obtain ⟨hi, hj⟩ := hl
    by_cases hli : l < i
    · rw [hA hli, zero_mul]
    · have hjl : j < l := by
        have := Fin.val_ne_of_ne hi
        have := Fin.val_ne_of_ne hj
        change j.val < l.val
        change ¬ l.val < i.val at hli
        omega
      rw [hB hjl, mul_zero]
  rw [Matrix.mul_apply, ← hs]
  simp [ij, dA, dB]

private theorem upper_mul_gap_two {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (dA : ∀ i, A i i = 1) (dB : ∀ i, B i i = 1)
    (i j k : Fin n) (hij : j.val = i.val + 1) (hjk : k.val = j.val + 1) :
    (A * B) i k = B i k + A i j * B j k + A i k := by
  have ij : i ≠ j := by intro h; subst j; omega
  have ik : i ≠ k := by intro h; subst k; omega
  have jk : j ≠ k := by intro h; subst k; omega
  have hs : (∑ l ∈ ({i,j,k} : Finset (Fin n)), A i l * B l k) =
      ∑ l, A i l * B l k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    obtain ⟨hi, hj, hk⟩ := hl
    by_cases hli : l < i
    · rw [hA hli, zero_mul]
    · have hkl : k < l := by
        have := Fin.val_ne_of_ne hi
        have := Fin.val_ne_of_ne hj
        have := Fin.val_ne_of_ne hk
        change k.val < l.val
        change ¬ l.val < i.val at hli
        omega
      rw [hB hkl, mul_zero]
  rw [Matrix.mul_apply, ← hs]
  simp [ij, ik, jk, dA, dB, add_assoc]

private theorem upper_square_gap_two {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : A.IsUpperTriangular) (dA : ∀ i, A i i = 1)
    (i j k : Fin n) (hij : j.val = i.val + 1) (hjk : k.val = j.val + 1) :
    (A ^ 2) i k = A i j * A j k := by
  rw [pow_two, upper_mul_gap_two A A hA hA dA dA i j k hij hjk]
  have hzero : A i k + A i k = 0 := CharTwo.add_self_eq_zero _
  linear_combination hzero

private theorem upper_commute_gap_two {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (dA : ∀ i, A i i = 1) (dB : ∀ i, B i i = 1)
    (i j k : Fin n) (hij : j.val = i.val + 1) (hjk : k.val = j.val + 1)
    (hc : Commute A B) : A i j * B j k = B i j * A j k := by
  have he := congrArg (fun C : Matrix (Fin n) (Fin n) (ZMod 2) => C i k) hc.eq
  rw [upper_mul_gap_two A B hA hB dA dB i j k hij hjk,
    upper_mul_gap_two B A hB hA dB dA i j k hij hjk] at he
  linear_combination he

private theorem degree_eq_four_of_displacement_entries {n : ℕ} (hn : 3 ≤ n)
    (D : ℕ → Matrix (Fin n) (Fin n) (ZMod 2))
    (hu : ∀ r, r + 1 < n → (D r).IsUpperTriangular)
    (hd : ∀ r, r + 1 < n → ∀ i, D r i i = 1)
    (he : ∀ r, r + 1 < n → ∀ i j : Fin n, j.val = i.val + 1 →
      D r i j = (if i.val = r then 1 else 0) +
        (if i.val + r + 2 = n then 1 else 0))
    (hs : ∀ r, r + 1 < n → D r ^ 2 = 1)
    (hc : ∀ r, r + 1 < n → ∀ s, s + 1 < n → Commute (D r) (D s)) : n = 4 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have ij : j.val = i.val + 1 := rfl
  have jk : k.val = j.val + 1 := rfl
  have h0 : 0 + 1 < n := by omega
  have h1 : 1 + 1 < n := by omega
  have hA01 := he 0 h0 i j ij
  have hA12 := he 0 h0 j k jk
  have hB01 := he 1 h1 i j ij
  have hB12 := he 1 h1 j k jk
  simp only [i, j] at hA01 hA12 hB01 hB12
  by_cases h3 : n = 3
  · have hz := congrArg (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => A i k) (hs 0 h0)
    rw [upper_square_gap_two _ (hu 0 h0) (hd 0 h0) i j k ij jk,
      hA01, hA12] at hz
    have hik : i ≠ k := by intro h; have := congrArg Fin.val h; dsimp [i,k] at this; omega
    norm_num [h3, Matrix.one_apply, hik] at hz
  · by_contra h4
    have hn5 : 5 ≤ n := by omega
    have hz := upper_commute_gap_two (D 0) (D 1) (hu 0 h0) (hu 1 h1)
      (hd 0 h0) (hd 1 h1) i j k ij jk (hc 0 h0 1 h1)
    rw [hA01, hA12, hB01, hB12] at hz
    norm_num [show 2 ≠ n by omega, show 3 ≠ n by omega, show 4 ≠ n by omega] at hz

end BinaryLinear.ElementaryOuterSylow


open Matrix
open scoped MatrixGroups
namespace BinaryLinear.ElementaryOuterSylow
open OuterCyclic Theory.SpecificGroups.LinearSylowNormalizers

private def reverseMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if i.rev = j then 1 else 0

private theorem reverseMatrix_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (i j : Fin n) : (reverseMatrix n * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, reverseMatrix]

private theorem mul_reverseMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (i j : Fin n) : (A * reverseMatrix n) i j = A i j.rev := by
  simp only [Matrix.mul_apply, reverseMatrix]
  have h (k : Fin n) : k.rev = j ↔ k = j.rev := by
    constructor <;> intro h <;> simpa using congrArg Fin.rev h
  simp [h]

private theorem reverseMatrix_sq (n : ℕ) : reverseMatrix n * reverseMatrix n = 1 := by
  ext i j
  simp [reverseMatrix_mul, reverseMatrix, Matrix.one_apply]

private def reverseSL (n : ℕ) : SL(n, ZMod 2) :=
  ⟨reverseMatrix n, by
    have he := congrArg Matrix.det (reverseMatrix_sq n)
    rw [Matrix.det_mul, Matrix.det_one] at he
    have hn : (reverseMatrix n).det ≠ 0 := by intro hz; simp [hz] at he
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn⟩

private theorem reverseSL_inv (n : ℕ) : (reverseSL n)⁻¹ = reverseSL n := by
  apply inv_eq_of_mul_eq_one_left
  exact Subtype.ext (reverseMatrix_sq n)

private theorem reverseSL_transpose (n : ℕ) :
    SpecialLinearGroup.transpose (reverseSL n) = reverseSL n := by
  apply Subtype.ext
  ext i j
  change (if j.rev = i then (1 : ZMod 2) else 0) = if i.rev = j then 1 else 0
  have he : j.rev = i ↔ i.rev = j := by
    constructor <;> intro h <;> simpa using (congrArg Fin.rev h).symm
  simp only [he]

private theorem graphSL_reverseSL (n : ℕ) : graphSL n (reverseSL n) = reverseSL n := by
  change (SpecialLinearGroup.transpose (reverseSL n))⁻¹ = _
  rw [reverseSL_transpose, reverseSL_inv]

private def reverseGraph (n : ℕ) : MulAut SL(n, ZMod 2) :=
  MulAut.conj (reverseSL n) * graphSL n

private theorem reverseGraph_apply {n : ℕ} (u : SL(n, ZMod 2)) (i j : Fin n) :
    (reverseGraph n u).val i j = u⁻¹.val j.rev i.rev := by
  change ((reverseSL n * graphSL n u) * (reverseSL n)⁻¹).val i j = _
  rw [reverseSL_inv]
  change ((reverseMatrix n * (graphSL n u).val) * reverseMatrix n) i j = _
  rw [mul_reverseMatrix, reverseMatrix_mul]
  have he : graphSL n u = SpecialLinearGroup.transpose u⁻¹ := by
    change (SpecialLinearGroup.transpose u)⁻¹ = SpecialLinearGroup.transpose u⁻¹
    apply inv_eq_of_mul_eq_one_right
    change SpecialLinearGroup.transpose u * SpecialLinearGroup.transpose u⁻¹ = 1
    apply Subtype.ext
    change u.val.transpose * u⁻¹.val.transpose = 1
    rw [← Matrix.transpose_mul]
    have hh : u⁻¹.val * u.val = 1 := congrArg Subtype.val (inv_mul_cancel u)
    rw [hh, Matrix.transpose_one]
  rw [he]
  rfl

private theorem reverseGraph_preserves {n : ℕ} (u : SL(n, ZMod 2))
    (hu : u ∈ unipotent n (ZMod 2)) : reverseGraph n u ∈ unipotent n (ZMod 2) := by
  obtain ⟨hb, hd⟩ := (mem_unipotent n (ZMod 2) u⁻¹).mp
    ((unipotent n (ZMod 2)).inv_mem hu)
  rw [mem_unipotent, mem_borel]
  constructor
  · intro i j hji
    rw [reverseGraph_apply]
    exact (mem_borel n (ZMod 2) u⁻¹).mp hb (by simpa using hji)
  · intro i
    rw [reverseGraph_apply, hd]

private theorem graph_inner_factor {n : ℕ} (g u : SL(n, ZMod 2)) :
    (graphSL n * MulAut.conj g) u =
      (MulAut.conj (graphSL n g * reverseSL n)) (reverseGraph n u) := by
  change graphSL n (g * u * g⁻¹) =
    (graphSL n g * reverseSL n) *
      (reverseSL n * graphSL n u * (reverseSL n)⁻¹) *
      (graphSL n g * reverseSL n)⁻¹
  rw [map_mul, map_mul, map_inv, reverseSL_inv]
  have hh : reverseSL n * reverseSL n = 1 := Subtype.ext (reverseMatrix_sq n)
  simp only [_root_.mul_inv_rev, reverseSL_inv]
  simp only [mul_assoc, ← mul_assoc (reverseSL n) (reverseSL n), hh, one_mul]

private theorem reverseGraph_involutive (n : ℕ) : Function.Involutive (reverseGraph n) := by
  intro u
  change reverseSL n * graphSL n (reverseSL n * graphSL n u * (reverseSL n)⁻¹) *
    (reverseSL n)⁻¹ = u
  rw [map_mul, map_mul, map_inv, graphSL_reverseSL]
  have hg : graphSL n (graphSL n u) = u := by
    have he := congrArg (fun a : MulAut SL(n, ZMod 2) => a u) (graphSL_sq n)
    exact he
  rw [hg, reverseSL_inv]
  have hh : reverseSL n * reverseSL n = 1 := Subtype.ext (reverseMatrix_sq n)
  simp only [← mul_assoc, hh, one_mul]
  rw [mul_assoc, hh, mul_one]

private theorem graph_inner_adjustment_unipotent {n : ℕ} (g : SL(n, ZMod 2))
    (hp : ∀ u ∈ unipotent n (ZMod 2),
      (graphSL n * MulAut.conj g) u ∈ unipotent n (ZMod 2)) :
    graphSL n g * reverseSL n ∈ unipotent n (ZMod 2) := by
  have hN : graphSL n g * reverseSL n ∈
      Subgroup.normalizer (unipotent n (ZMod 2) : Set SL(n, ZMod 2)) := by
    apply Subgroup.mem_normalizer_fintype
    intro u hu
    have h := hp _ (reverseGraph_preserves u hu)
    rw [graph_inner_factor, reverseGraph_involutive] at h
    exact h
  rw [normalizer_unipotent] at hN
  rw [mem_unipotent]
  refine ⟨hN, fun i => ?_⟩
  have he := (graphSL n g * reverseSL n).property
  rw [Matrix.det_of_isUpperTriangular ((mem_borel _ _ _).mp hN)] at he
  have hn : (∏ j, (graphSL n g * reverseSL n).val j j) ≠ 0 := by rw [he]; exact one_ne_zero
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _
    (Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i))

private theorem unipotent_mul_edge {n : ℕ} (u v : SL(n, ZMod 2))
    (hu : u ∈ unipotent n (ZMod 2)) (hv : v ∈ unipotent n (ZMod 2))
    (i j : Fin n) (hij : j.val = i.val + 1) :
    (u * v).val i j = v.val i j + u.val i j := by
  obtain ⟨hu, du⟩ := (mem_unipotent _ _ _).mp hu
  obtain ⟨hv, dv⟩ := (mem_unipotent _ _ _).mp hv
  exact upper_mul_gap_one u.val v.val ((mem_borel _ _ _).mp hu)
    ((mem_borel _ _ _).mp hv) du dv i j hij

private theorem unipotent_inv_edge {n : ℕ} (u : SL(n, ZMod 2))
    (hu : u ∈ unipotent n (ZMod 2)) (i j : Fin n)
    (hij : j.val = i.val + 1) : u⁻¹.val i j = u.val i j := by
  have he := unipotent_mul_edge u u⁻¹ hu ((unipotent n (ZMod 2)).inv_mem hu) i j hij
  have hne : i ≠ j := by intro h; subst j; omega
  rw [mul_inv_cancel] at he
  have hz : u⁻¹.val i j + u.val i j = 0 := by
    rw [← he]
    exact Matrix.one_apply_ne hne
  exact CharTwo.add_eq_zero.mp hz

private theorem unipotent_conj_edge {n : ℕ} (a u : SL(n, ZMod 2))
    (ha : a ∈ unipotent n (ZMod 2)) (hu : u ∈ unipotent n (ZMod 2))
    (i j : Fin n) (hij : j.val = i.val + 1) :
    (MulAut.conj a u).val i j = u.val i j := by
  change (a * u * a⁻¹).val i j = _
  rw [unipotent_mul_edge _ _ ((unipotent n (ZMod 2)).mul_mem ha hu)
    ((unipotent n (ZMod 2)).inv_mem ha) i j hij,
    unipotent_mul_edge _ _ ha hu i j hij, unipotent_inv_edge a ha i j hij]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

private theorem graph_inner_edge {n : ℕ} (g : SL(n, ZMod 2))
    (hp : ∀ u ∈ unipotent n (ZMod 2),
      (graphSL n * MulAut.conj g) u ∈ unipotent n (ZMod 2))
    (u : SL(n, ZMod 2)) (hu : u ∈ unipotent n (ZMod 2))
    (i j : Fin n) (hij : j.val = i.val + 1) :
    ((graphSL n * MulAut.conj g) u).val i j = u.val j.rev i.rev := by
  rw [graph_inner_factor,
    unipotent_conj_edge _ _ (graph_inner_adjustment_unipotent g hp)
      (reverseGraph_preserves u hu) i j hij,
    reverseGraph_apply, unipotent_inv_edge u hu]
  simp only [Fin.val_rev]
  have := i.isLt
  have := j.isLt
  omega

private def edgeTransvection (n r : ℕ) (hr : r + 1 < n) : SL(n, ZMod 2) :=
  SpecialLinearGroup.transvection (i := ⟨r, by omega⟩) (j := ⟨r+1, hr⟩)
    (by intro h; have he : r = r+1 := congrArg Fin.val h; omega) 1

private theorem edgeTransvection_mem (n r : ℕ) (hr : r + 1 < n) :
    edgeTransvection n r hr ∈ unipotent n (ZMod 2) := by
  rw [mem_unipotent, mem_borel]
  constructor
  · exact Matrix.blockTriangular_transvection (by change r ≤ r+1; omega) 1
  · intro i
    change (1 + Matrix.single (⟨r, by omega⟩ : Fin n) (⟨r+1, hr⟩ : Fin n) (1 : ZMod 2)) i i = 1
    simp [Matrix.single_apply]
    intro h
    have hi := congrArg Fin.val h
    apply Fin.ne_of_val_ne
    change r = i.val at hi
    change r+1 ≠ i.val
    omega

private theorem edgeTransvection_entry (n r : ℕ) (hr : r+1<n)
    (i j : Fin n) (hij : j.val = i.val + 1) :
    (edgeTransvection n r hr).val i j = if i.val = r then 1 else 0 := by
  have hne : i ≠ j := by intro h; subst j; omega
  change (1 + Matrix.single (⟨r, by omega⟩ : Fin n) (⟨r+1, hr⟩ : Fin n) (1 : ZMod 2)) i j = _
  simp only [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.single_apply]
  by_cases hi : i.val = r
  · have hi' : i = ⟨r, by omega⟩ := Fin.ext hi
    have hjv : j.val = r+1 := by omega
    have hj' : j = ⟨r+1,hr⟩ := Fin.ext hjv
    simp [hi', hj']
  · have hi' : (⟨r, by omega⟩ : Fin n) ≠ i := fun h => hi (congrArg Fin.val h.symm)
    simp [hi, hi']

private theorem degree_eq_four_unipotent {n : ℕ} (hn : 3 ≤ n) (g : SL(n, ZMod 2))
    (hp : ∀ u ∈ unipotent n (ZMod 2),
      (graphSL n * MulAut.conj g) u ∈ unipotent n (ZMod 2))
    (hs : ∀ u ∈ unipotent n (ZMod 2),
      ((graphSL n * MulAut.conj g) u * u⁻¹) ^ 2 = 1)
    (hc : ∀ u ∈ unipotent n (ZMod 2), ∀ v ∈ unipotent n (ZMod 2),
      Commute ((graphSL n * MulAut.conj g) u * u⁻¹)
        ((graphSL n * MulAut.conj g) v * v⁻¹)) : n = 4 := by
  let t (r : ℕ) : SL(n, ZMod 2) := if hr : r+1<n then edgeTransvection n r hr else 1
  have ht (r : ℕ) : t r ∈ unipotent n (ZMod 2) := by
    dsimp [t]
    split
    · exact edgeTransvection_mem _ _ _
    · exact (unipotent n (ZMod 2)).one_mem
  let d (r : ℕ) := (graphSL n * MulAut.conj g) (t r) * (t r)⁻¹
  have hd (r : ℕ) : d r ∈ unipotent n (ZMod 2) :=
    (unipotent n (ZMod 2)).mul_mem (hp _ (ht r))
      ((unipotent n (ZMod 2)).inv_mem (ht r))
  apply degree_eq_four_of_displacement_entries hn (fun r => (d r).val)
  · intro r _
    exact (mem_borel _ _ _).mp ((mem_unipotent _ _ _).mp (hd r)).1
  · intro r _
    exact ((mem_unipotent _ _ _).mp (hd r)).2
  · intro r hr i j hij
    change ((graphSL n * MulAut.conj g) (t r) * (t r)⁻¹).val i j = _
    rw [unipotent_mul_edge _ _ (hp _ (ht r)) ((unipotent n (ZMod 2)).inv_mem (ht r)) i j hij,
      unipotent_inv_edge _ (ht r) i j hij, graph_inner_edge g hp _ (ht r) i j hij]
    have hrev : i.rev.val = j.rev.val + 1 := by
      simp only [Fin.val_rev]
      have := i.isLt
      have := j.isLt
      omega
    dsimp only [t]
    rw [dif_pos hr, edgeTransvection_entry _ _ _ i j hij,
      edgeTransvection_entry _ _ _ j.rev i.rev hrev]
    congr 1
    have he : j.rev.val = r ↔ i.val + r + 2 = n := by
      simp only [Fin.val_rev]
      have := j.isLt
      omega
    simp only [he]
  · intro r _
    exact congrArg Subtype.val (hs _ (ht r))
  · intro r _ s _
    exact congrArg Subtype.val (hc _ (ht r) _ (ht s)).eq

private theorem degree_eq_four_sylowSL {n : ℕ} (hn : 3 ≤ n) (P : Sylow 2 SL(n, ZMod 2))
    (g : SL(n, ZMod 2))
    (hp : ∀ u ∈ (P : Subgroup SL(n, ZMod 2)),
      (graphSL n * MulAut.conj g) u ∈ (P : Subgroup SL(n, ZMod 2)))
    (hs : ∀ u ∈ (P : Subgroup SL(n, ZMod 2)),
      ((graphSL n * MulAut.conj g) u * u⁻¹) ^ 2 = 1)
    (hc : ∀ u ∈ (P : Subgroup SL(n, ZMod 2)), ∀ v ∈ (P : Subgroup SL(n, ZMod 2)),
      Commute ((graphSL n * MulAut.conj g) u * u⁻¹)
        ((graphSL n * MulAut.conj g) v * v⁻¹)) : n = 4 := by
  obtain ⟨c, hcP⟩ := MulAction.exists_smul_eq SL(n, ZMod 2)
    (standardSylow n (ZMod 2) (by omega)) P
  have haction : MulDistribMulAction.toMonoidEnd (MulAut SL(n, ZMod 2))
      SL(n, ZMod 2) (MulAut.conj c) = (MulAut.conj c).toMonoidHom := by
    ext u
    rfl
  have hP : (unipotent n (ZMod 2)).map (MulAut.conj c).toMonoidHom =
      (P : Subgroup SL(n, ZMod 2)) := by
    simpa only [Sylow.coe_subgroup_smul, coe_standardSylow, Subgroup.pointwise_smul_def,
      haction] using
      congrArg (fun S : Sylow 2 SL(n, ZMod 2) => (S : Subgroup SL(n, ZMod 2))) hcP
  have hmem (u : SL(n, ZMod 2)) (hu : u ∈ unipotent n (ZMod 2)) :
      c * u * c⁻¹ ∈ (P : Subgroup SL(n, ZMod 2)) := by
    rw [← hP]
    exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hu
  have hmem' (u : SL(n, ZMod 2)) (hu : u ∈ (P : Subgroup SL(n, ZMod 2))) :
      c⁻¹ * u * c ∈ unipotent n (ZMod 2) := by
    rw [← hP, Subgroup.mem_map_equiv] at hu
    exact hu
  let a := graphSL n * MulAut.conj g
  let g' := graphSL n c⁻¹ * g * c
  let b := graphSL n * MulAut.conj g'
  have htwice (u : SL(n, ZMod 2)) : graphSL n (graphSL n u) = u :=
    congrArg (fun a : MulAut SL(n, ZMod 2) => a u) (graphSL_sq n)
  have hb (u : SL(n, ZMod 2)) : b u = c⁻¹ * a (c * u * c⁻¹) * c := by
    change graphSL n ((graphSL n c⁻¹ * g * c) * u *
      (graphSL n c⁻¹ * g * c)⁻¹) = c⁻¹ * graphSL n (g * (c * u * c⁻¹) * g⁻¹) * c
    simp only [map_mul, map_inv, _root_.mul_inv_rev, htwice]
    group
  have hd (u : SL(n, ZMod 2)) : b u * u⁻¹ =
      (MulAut.conj c⁻¹) (a (c * u * c⁻¹) * (c * u * c⁻¹)⁻¹) := by
    rw [hb]
    change _ = c⁻¹ * _ * (c⁻¹)⁻¹
    group
  apply degree_eq_four_unipotent hn g'
  · intro u hu
    change b u ∈ _
    rw [hb]
    exact hmem' _ (hp _ (hmem u hu))
  · intro u hu
    change (b u * u⁻¹) ^ 2 = 1
    rw [hd, ← map_pow, hs _ (hmem u hu), map_one]
  · intro u hu v hv
    change Commute (b u * u⁻¹) (b v * v⁻¹)
    rw [hd, hd]
    exact (hc _ (hmem u hu) _ (hmem v hv)).map (MulAut.conj c⁻¹).toMonoidHom

private theorem graphSylowDegreeBound_concrete
    (n : ℕ) (hn : 3 ≤ n) (P : Sylow 2 (LinearGroup n)) (g : LinearGroup n)
    (hp : ∀ u ∈ (P : Subgroup (LinearGroup n)),
      (graphLinear n * MulAut.conj g) u ∈ (P : Subgroup (LinearGroup n)))
    (hs : ∀ u ∈ (P : Subgroup (LinearGroup n)),
      ((graphLinear n * MulAut.conj g) u * u⁻¹) ^ 2 = 1)
    (hc : ∀ u ∈ (P : Subgroup (LinearGroup n)), ∀ v ∈ (P : Subgroup (LinearGroup n)),
      Commute ((graphLinear n * MulAut.conj g) u * u⁻¹)
        ((graphLinear n * MulAut.conj g) v * v⁻¹)) : n = 4 := by
  let e := slEquivLinear n
  let : Finite (LinearGroup n) := Finite.of_surjective e e.surjective
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ (u : SL(n, ZMod 2)) : u ∈ (Q : Subgroup SL(n, ZMod 2)) ↔
      e u ∈ (P : Subgroup (LinearGroup n)) := by
    change u ∈ (P : Subgroup (LinearGroup n)).map e.symm.toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    rfl
  let a := graphLinear n * MulAut.conj g
  let b := graphSL n * MulAut.conj (e.symm g)
  have hb (u : SL(n, ZMod 2)) : e (b u) = a (e u) := by
    change e (graphSL n (e.symm g * u * (e.symm g)⁻¹)) =
      graphLinear n (g * e u * g⁻¹)
    have hg (x : SL(n, ZMod 2)) : e (graphSL n x) = graphLinear n (e x) :=
      (graphLinear_slEquivLinear n x).symm
    rw [hg]
    simp only [map_mul, map_inv, e.apply_symm_apply]
  apply degree_eq_four_sylowSL hn Q (e.symm g)
  · intro u hu
    apply (hQ _).mpr
    change e (b u) ∈ _
    rw [hb]
    exact hp _ ((hQ _).mp hu)
  · intro u hu
    apply e.injective
    change e ((b u * u⁻¹)^2) = e 1
    rw [map_pow, map_mul, map_inv, hb, map_one]
    exact hs _ ((hQ _).mp hu)
  · intro u hu v hv
    apply e.injective
    change e ((b u * u⁻¹) * (b v * v⁻¹)) = e ((b v * v⁻¹) * (b u * u⁻¹))
    simp only [map_mul, map_inv, hb]
    exact (hc _ ((hQ _).mp hu) _ ((hQ _).mp hv)).eq

/-- The graph-coset displacement calculation for an actual binary Sylow. -/
theorem graphSylowDegreeBound : GraphSylowDegreeBound :=
  graphSylowDegreeBound_concrete

/-- An elementary outer action on a Sylow of a full binary linear group of
at least degree three forces degree four. Both the action and equivalence are
those supplied by the caller. -/
theorem finrank_eq_four {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (a : Theory.GroupTheory.ElementaryOuterSylowAction H)
    (e : H ≃* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hd : 3 ≤ Module.finrank (ZMod 2) V) : Module.finrank (ZMod 2) V = 4 :=
  finrank_eq_four_of_graphSylowDegreeBound graphSylowDegreeBound a e hd

end BinaryLinear.ElementaryOuterSylow
