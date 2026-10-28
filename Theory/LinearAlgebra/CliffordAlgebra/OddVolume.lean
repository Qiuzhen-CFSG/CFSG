module

public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The odd-dimensional Clifford volume unit

For a finite-dimensional nondegenerate quadratic space over a field in which
two is invertible, an orthogonal basis consists of anisotropic vectors.  This
module forms the corresponding Clifford volume as a product of vector units,
proves that it belongs to Mathlib's generated `lipschitzGroup`, and records
that its `ZMod 2` degree is the basis length.  In odd dimension, moving an
embedded vector through that product contributes the sign
`(-1)^(finrank - 1) = 1`, so the volume commutes with every embedded vector.

The resulting central odd Lipschitz unit is the parity-adjustment witness used
after Cartan--Dieudonne factorization in the finite reverse-normalizer theorem:
multiplying by it changes Clifford parity without changing ordinary
conjugation.  The scalar-unit lemma at the end supplies the other ingredient
of that assembly: any nonzero scalar Clifford unit is a product of two
anisotropic vector units.  The proof uses Mathlib's exact generated
`lipschitzGroup`; no alternative normalizer is introduced.
-/

open CliffordAlgebra

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

/-- The Clifford unit represented by an anisotropic embedded vector. -/
public noncomputable def cliffordAnisotropicVectorUnit
    (a : {v : V // Q v ≠ 0}) : (CliffordAlgebra Q)ˣ := by
  letI : Invertible (Q a.1) := invertibleOfNonzero a.2
  letI : Invertible (CliffordAlgebra.ι Q a.1) :=
    CliffordAlgebra.invertibleιOfInvertible Q a.1
  exact unitOfInvertible (CliffordAlgebra.ι Q a.1)

omit [Invertible (2 : k)] [FiniteDimensional k V] in
@[simp] public lemma cliffordAnisotropicVectorUnit_coe
    (a : {v : V // Q v ≠ 0}) :
    (cliffordAnisotropicVectorUnit a : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q a.1 := by
  simp [cliffordAnisotropicVectorUnit]

omit [Invertible (2 : k)] [FiniteDimensional k V] in
public lemma cliffordAnisotropicVectorUnit_mem_lipschitzGroup
    (a : {v : V // Q v ≠ 0}) :
    cliffordAnisotropicVectorUnit a ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  exact ⟨a.1, cliffordAnisotropicVectorUnit_coe a⟩

/-- The Clifford volume unit obtained by multiplying an anisotropic basis in
the order of its `Fin` indices. -/
public noncomputable def cliffordVolumeUnit
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hbq : ∀ i, Q (b i) ≠ 0) : (CliffordAlgebra Q)ˣ :=
  (List.ofFn fun i =>
    cliffordAnisotropicVectorUnit (Q := Q) ⟨b i, hbq i⟩).prod

omit [Invertible (2 : k)] [FiniteDimensional k V] in
@[simp] public lemma cliffordVolumeUnit_coe
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hbq : ∀ i, Q (b i) ≠ 0) :
    (cliffordVolumeUnit b hbq : CliffordAlgebra Q) =
      (List.ofFn fun i => CliffordAlgebra.ι Q (b i)).prod := by
  rw [cliffordVolumeUnit]
  change Units.coeHom (CliffordAlgebra Q)
      (List.ofFn fun i =>
        cliffordAnisotropicVectorUnit (Q := Q) ⟨b i, hbq i⟩).prod = _
  rw [map_list_prod]
  rw [List.map_ofFn]
  apply congrArg List.prod
  rw [List.ofFn_inj]
  funext i
  exact cliffordAnisotropicVectorUnit_coe _

omit [Invertible (2 : k)] [FiniteDimensional k V] in
/-- The orthogonal-basis volume is in Mathlib's generated Lipschitz group. -/
public lemma cliffordVolumeUnit_mem_lipschitzGroup
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hbq : ∀ i, Q (b i) ≠ 0) :
    cliffordVolumeUnit b hbq ∈ lipschitzGroup Q := by
  apply (lipschitzGroup Q).list_prod_mem
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact cliffordAnisotropicVectorUnit_mem_lipschitzGroup _

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma iotaList_prod_mem_evenOdd (l : List V) :
    (l.map (CliffordAlgebra.ι Q)).prod ∈
      CliffordAlgebra.evenOdd Q (l.length : ZMod 2) := by
  induction l with
  | nil => simpa using (SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q))
  | cons a l ih =>
      simpa [add_comm] using SetLike.mul_mem_graded
        (CliffordAlgebra.ι_mem_evenOdd_one Q a) ih

omit [Invertible (2 : k)] [FiniteDimensional k V] in
/-- The degree of the orthogonal-basis volume is its basis length modulo two. -/
public lemma cliffordVolumeUnit_mem_evenOdd
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hbq : ∀ i, Q (b i) ≠ 0) :
    (cliffordVolumeUnit b hbq : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (Module.finrank k V : ZMod 2) := by
  rw [cliffordVolumeUnit_coe]
  have hlist : List.ofFn ((CliffordAlgebra.ι Q) ∘ b) =
      List.ofFn (fun i => CliffordAlgebra.ι Q (b i)) := by
    rw [List.ofFn_inj]
    funext i
    rfl
  simpa only [List.map_ofFn, List.length_ofFn, hlist] using
    (iotaList_prod_mem_evenOdd (Q := Q) (List.ofFn b))

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma iota_anti_prod (t : CliffordAlgebra Q)
    (l : List (CliffordAlgebra Q))
    (hanti : ∀ z ∈ l, t * z = -z * t) :
    t * l.prod = (-1 : k) ^ l.length • (l.prod * t) := by
  induction l with
  | nil => simp
  | cons z l ih =>
    calc
      t * (z * l.prod) = (t * z) * l.prod := by rw [mul_assoc]
      _ = (-z * t) * l.prod := by rw [hanti z (by simp)]
      _ = -(z * (t * l.prod)) := by noncomm_ring
      _ = -(z * ((-1 : k) ^ l.length • (l.prod * t))) := by
        rw [ih (fun y hy => hanti y (by simp [hy]))]
      _ = (-1 : k) ^ (l.length + 1) • (z * l.prod * t) := by
        simp only [Algebra.smul_def, pow_succ]
        simp only [map_mul, map_neg, map_one]
        rw [← mul_assoc]
        rw [← Algebra.commutes ((-1 : k) ^ l.length) z]
        noncomm_ring

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma iota_mul_iotaList_prod_of_mem
    {l : List V} (hpair : l.Pairwise Q.IsOrtho) (a : V) (ha : a ∈ l) :
    CliffordAlgebra.ι Q a * (l.map (CliffordAlgebra.ι Q)).prod =
      (-1 : k) ^ (l.length - 1) •
        ((l.map (CliffordAlgebra.ι Q)).prod * CliffordAlgebra.ι Q a) := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    obtain rfl | ⟨hne, ha'⟩ := List.eq_or_ne_mem_of_mem ha
    · rw [List.map_cons, List.prod_cons]
      have hrest : ∀ c ∈ l, Q.IsOrtho a c := by
        intro c hc
        exact (List.pairwise_cons.mp hpair).1 c hc
      have hanti := iota_anti_prod (Q := Q) (CliffordAlgebra.ι Q a)
        (l.map (CliffordAlgebra.ι Q)) (by
          intro z hz
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
          simpa only [neg_mul] using
            (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (hrest c hc)))
      simp only [List.length_map] at hanti
      calc
        CliffordAlgebra.ι Q a *
            (CliffordAlgebra.ι Q a *
              (l.map (CliffordAlgebra.ι Q)).prod) =
            (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a) *
              (l.map (CliffordAlgebra.ι Q)).prod := by rw [mul_assoc]
        _ = algebraMap k _ (Q a) *
              (l.map (CliffordAlgebra.ι Q)).prod := by
              rw [CliffordAlgebra.ι_sq_scalar]
        _ = (-1 : k) ^ l.length •
              (CliffordAlgebra.ι Q a *
                (l.map (CliffordAlgebra.ι Q)).prod *
                  CliffordAlgebra.ι Q a) := by
              calc
                algebraMap k _ (Q a) *
                    (l.map (CliffordAlgebra.ι Q)).prod =
                    (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a) *
                      (l.map (CliffordAlgebra.ι Q)).prod := by
                      rw [CliffordAlgebra.ι_sq_scalar]
                _ = CliffordAlgebra.ι Q a *
                    (CliffordAlgebra.ι Q a *
                      (l.map (CliffordAlgebra.ι Q)).prod) := by rw [mul_assoc]
                _ = CliffordAlgebra.ι Q a *
                    ((-1 : k) ^ l.length •
                      ((l.map (CliffordAlgebra.ι Q)).prod *
                        CliffordAlgebra.ι Q a)) := by rw [hanti]
                _ = _ := by
                  rw [mul_smul_comm]
                  simp only [mul_assoc]
        _ = (-1 : k) ^ ((a :: l).length - 1) •
              (CliffordAlgebra.ι Q a *
                (l.map (CliffordAlgebra.ι Q)).prod *
                  CliffordAlgebra.ι Q a) := by simp
    · rw [List.map_cons, List.prod_cons]
      have hab : Q.IsOrtho a b :=
        (List.pairwise_cons.mp hpair).1 a ha' |>.symm
      calc
        CliffordAlgebra.ι Q a *
            (CliffordAlgebra.ι Q b *
              (l.map (CliffordAlgebra.ι Q)).prod) =
            (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
              (l.map (CliffordAlgebra.ι Q)).prod := by rw [mul_assoc]
        _ = (-(CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a)) *
              (l.map (CliffordAlgebra.ι Q)).prod := by
              rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hab]
        _ = -(CliffordAlgebra.ι Q b *
              (CliffordAlgebra.ι Q a *
                (l.map (CliffordAlgebra.ι Q)).prod)) := by noncomm_ring
        _ = -(CliffordAlgebra.ι Q b *
              ((-1 : k) ^ (l.length - 1) •
                ((l.map (CliffordAlgebra.ι Q)).prod *
                  CliffordAlgebra.ι Q a))) := by
              rw [ih (List.pairwise_cons.mp hpair).2 ha']
        _ = (-1 : k) ^ ((b :: l).length - 1) •
              (CliffordAlgebra.ι Q b *
                (l.map (CliffordAlgebra.ι Q)).prod *
                  CliffordAlgebra.ι Q a) := by
              have hlen : 0 < l.length := List.length_pos_iff.mpr (by
                intro hz
                subst hz
                simp at ha')
              have hpow : (-1 : k) ^ l.length =
                  -((-1 : k) ^ (l.length - 1)) := by
                have hEq : l.length = (l.length - 1) + 1 := by omega
                rw [hEq, pow_succ]
                simp
              have hcons : (b :: l).length - 1 = l.length := by simp
              rw [hcons, mul_smul_comm, ← neg_smul, hpow]
              simp only [mul_assoc]

omit [Invertible (2 : k)] [FiniteDimensional k V] in
/-- In odd basis length, the Clifford volume commutes with every embedded
vector. -/
public lemma cliffordVolumeUnit_commute_ι
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hborth : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
    (hbq : ∀ i, Q (b i) ≠ 0)
    (hodd : Odd (Module.finrank k V)) (v : V) :
    Commute (cliffordVolumeUnit b hbq : CliffordAlgebra Q)
      (CliffordAlgebra.ι Q v) := by
  let l : List V := List.ofFn fun i => b i
  have hpair : l.Pairwise Q.IsOrtho := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hborth i j hij.ne
  have hbcomm (i : Fin (Module.finrank k V)) :
      CliffordAlgebra.ι Q (b i) *
          (l.map (CliffordAlgebra.ι Q)).prod =
        (l.map (CliffordAlgebra.ι Q)).prod *
          CliffordAlgebra.ι Q (b i) := by
    rw [iota_mul_iotaList_prod_of_mem hpair (b i) (by
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩)]
    have hs : (-1 : k) ^ (l.length - 1) = 1 := by
      apply Even.neg_one_pow
      rcases hodd with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      simp only [l, List.length_ofFn]
      omega
    rw [hs, one_smul]
  rw [cliffordVolumeUnit_coe]
  change Commute (List.ofFn fun i => CliffordAlgebra.ι Q (b i)).prod
    (CliffordAlgebra.ι Q v)
  rw [show (List.ofFn fun i => CliffordAlgebra.ι Q (b i)) =
      l.map (CliffordAlgebra.ι Q) by simp [l, List.ofFn_eq_map]]
  change (l.map (CliffordAlgebra.ι Q)).prod * CliffordAlgebra.ι Q v =
    CliffordAlgebra.ι Q v * (l.map (CliffordAlgebra.ι Q)).prod
  rw [← b.sum_repr v]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul,
    smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z => (b.repr v) i • z) (hbcomm i).symm

omit [FiniteDimensional k V] in
/-- A scalar Clifford unit is in the generated Lipschitz group when the
quadratic space contains an anisotropic vector. -/
public theorem cliffordScalarUnit_mem_lipschitzGroup_of_anisotropic
    (v : V) (hv : Q v ≠ 0) (z : (CliffordAlgebra Q)ˣ) (a : k)
    (hz : (z : CliffordAlgebra Q) =
      algebraMap k (CliffordAlgebra Q) a) :
    z ∈ lipschitzGroup Q := by
  let _ : Nontrivial (CliffordAlgebra Q) :=
    (CliffordAlgebra.equivExterior Q).symm.injective.nontrivial
  have ha : a ≠ 0 := by
    intro ha
    have hz0 : (z : CliffordAlgebra Q) = 0 := by simp [hz, ha]
    exact z.ne_zero hz0
  let c : k := a * (Q v)⁻¹
  have hc : c ≠ 0 := mul_ne_zero ha (inv_ne_zero hv)
  have hcv : Q (c • v) ≠ 0 := by
    rw [QuadraticMap.map_smul]
    exact mul_ne_zero (mul_ne_zero hc hc) hv
  let uv := cliffordAnisotropicVectorUnit (Q := Q) ⟨v, hv⟩
  let ucv := cliffordAnisotropicVectorUnit (Q := Q) ⟨c • v, hcv⟩
  have huv : uv ∈ lipschitzGroup Q :=
    cliffordAnisotropicVectorUnit_mem_lipschitzGroup _
  have hucv : ucv ∈ lipschitzGroup Q :=
    cliffordAnisotropicVectorUnit_mem_lipschitzGroup _
  have hprod : z = ucv * uv := by
    apply Units.ext
    rw [hz, Units.val_mul]
    simp only [ucv, uv, cliffordAnisotropicVectorUnit_coe, map_smul,
      Algebra.smul_def, mul_assoc, CliffordAlgebra.ι_sq_scalar, ← map_mul]
    congr 1
    simp [c, hv]
  rw [hprod]
  exact (lipschitzGroup Q).mul_mem hucv huv

/-- In a positive-dimensional nondegenerate quadratic space, every scalar
Clifford unit belongs to Mathlib's generated Lipschitz group. -/
public theorem cliffordScalarUnit_mem_lipschitzGroup
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (z : (CliffordAlgebra Q)ˣ) (a : k)
    (hz : (z : CliffordAlgebra Q) =
      algebraMap k (CliffordAlgebra Q) a) :
    z ∈ lipschitzGroup Q := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := QuadraticMap.associated Q)
    (QuadraticForm.associated_isSymm k Q)
  have hsep : (QuadraticMap.associated Q).SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff).mpr hQ).1
  let i : Fin (Module.finrank k V) := ⟨0, hpos⟩
  have hi := hb.not_isOrtho_basis_self_of_separatingLeft hsep i
  have hbi : Q (b i) ≠ 0 := by
    simpa [QuadraticMap.associated_eq_self_apply] using hi
  exact cliffordScalarUnit_mem_lipschitzGroup_of_anisotropic
    (b i) hbi z a hz

/-- A nondegenerate odd-dimensional quadratic space has a central odd unit in
Mathlib's generated Lipschitz group. -/
public theorem exists_odd_cliffordVolumeUnit
    (hQ : Q.Nondegenerate) (hodd : Odd (Module.finrank k V)) :
    ∃ omega : (CliffordAlgebra Q)ˣ,
      omega ∈ lipschitzGroup Q ∧
      (omega : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 1 ∧
      ∀ v : V, Commute (omega : CliffordAlgebra Q)
        (CliffordAlgebra.ι Q v) := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := QuadraticMap.associated Q)
    (QuadraticForm.associated_isSymm k Q)
  have hsep : (QuadraticMap.associated Q).SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff).mpr hQ).1
  have hbq : ∀ i, Q (b i) ≠ 0 := by
    intro i
    have hi := hb.not_isOrtho_basis_self_of_separatingLeft hsep i
    simpa [QuadraticMap.associated_eq_self_apply] using hi
  have hborth : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j) := by
    intro i j hij
    exact QuadraticMap.associated_isOrtho.mp (hb hij)
  refine ⟨cliffordVolumeUnit b hbq,
    cliffordVolumeUnit_mem_lipschitzGroup b hbq, ?_, ?_⟩
  · have hgrade := cliffordVolumeUnit_mem_evenOdd b hbq
    have hcast : (Module.finrank k V : ZMod 2) = 1 :=
      hodd.natCast_zmod_two
    rw [← hcast]
    exact hgrade
  · exact cliffordVolumeUnit_commute_ι b hborth hbq hodd

end Theory.AlgebraicGroup
