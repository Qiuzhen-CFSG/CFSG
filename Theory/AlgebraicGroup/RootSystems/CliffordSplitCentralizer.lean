module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitPBW
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.Tactic.NoncommRing

/-!
# Scalar centralizer in a split even Clifford algebra

For a finite-dimensional quadratic space equipped with an explicit split
witness, an even Clifford element that commutes with every embedded vector is
scalar.  The proof is characteristic-free.  First, induction on the even
Clifford filtration identifies left contraction by the polar form with the
commutator by a vector.  Splitness makes the polar map onto the full dual, so
all contractions of the corresponding exterior-algebra element vanish under
the change-of-form equivalence.  The ordered exterior PBW basis then shows
that every nonempty monomial coefficient is zero, leaving the scalar
coefficient only.  This theorem is the lower-layer centralizer input for the
split Lipschitz normalizer and Spin-kernel constructions.

The contraction/PBW argument is extracted from the former private proof in
`AlgebraicGroups.EvenSpinActionKernel`; no characteristic or invertibility of
`2` is used.
-/

universe u

open CliffordAlgebra

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable {Q : QuadraticForm k V}

private theorem contractLeft_eq_commutator_of_mem_even
    (x : CliffordAlgebra Q) (hx : x ∈ CliffordAlgebra.even Q) (v : V) :
    CliffordAlgebra.contractLeft (Q.polarBilin v) x =
      CliffordAlgebra.ι Q v * x - x * CliffordAlgebra.ι Q v := by
  change x ∈ CliffordAlgebra.evenOdd Q 0 at hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap, Algebra.commutes]
  | add x y hx hy ihx ihy => simp only [map_add, mul_add, add_mul, ihx, ihy]; abel
  | ι_mul_ι_mul a b x hx ih =>
      simp only [mul_assoc]
      rw [CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, ih]
      simp only [QuadraticMap.polarBilin_apply_apply, Algebra.smul_def]
      have hva : algebraMap k (CliffordAlgebra Q) (QuadraticMap.polar Q v a) =
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a +
            CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q v :=
        (CliffordAlgebra.ι_mul_ι_add_swap v a).symm
      have hvb : algebraMap k (CliffordAlgebra Q) (QuadraticMap.polar Q v b) =
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q b +
            CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v :=
        (CliffordAlgebra.ι_mul_ι_add_swap v b).symm
      rw [hva, hvb]
      noncomm_ring

section ExteriorBasis

variable {I : Type*} [LinearOrder I] (b : Module.Basis I k V)

private theorem exteriorBasis_singleton (i : I) :
    b.ExteriorAlgebra ({i} : Finset I) =
      ExteriorAlgebra.ι k (b i) := by
  calc
    b.ExteriorAlgebra ({i} : Finset I) =
        ExteriorAlgebra.ιMulti_family k 1 b
          (Set.powersetCard.ofCard (by simp : ({i} : Finset I).card = 1)) :=
      ExteriorAlgebra.basis_apply_ofCard b _
    _ = ExteriorAlgebra.ι k (b i) := by
      change ExteriorAlgebra.ιMulti k 1 _ = _
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.orderEmbOfFin_apply]

private theorem exteriorBasis_insert_min (i : I) (s : Finset I)
    (hi : ∀ j ∈ s, i < j) :
    b.ExteriorAlgebra (insert i s) =
      ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra s := by
  have his : i ∉ s := fun his => (hi i his).false
  have hle : ∀ j ∈ s, i ≤ j := fun j hj => (hi j hj).le
  have hcard : (insert i s).card = s.card + 1 :=
    Finset.card_insert_of_notMem his
  calc
    b.ExteriorAlgebra (insert i s) =
        ExteriorAlgebra.ιMulti_family k (s.card + 1) b
          (Set.powersetCard.ofCard hcard) :=
      ExteriorAlgebra.basis_apply_ofCard b hcard
    _ = ExteriorAlgebra.ι k (b i) *
        ExteriorAlgebra.ιMulti_family k s.card b
          (Set.powersetCard.ofCard rfl) := by
      change ExteriorAlgebra.ιMulti k (s.card + 1) _ = _
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 1
      · simp [
          Set.powersetCard.ofFinEmbEquiv_symm_apply,
          Finset.orderEmbOfFin_apply, Finset.sort_insert (r := (· ≤ ·)) hle his]
      · congr 1
        ext j
        simp [Matrix.vecTail, Set.powersetCard.ofFinEmbEquiv_symm_apply,
          Finset.orderEmbOfFin_apply,
          Finset.sort_insert (r := (· ≤ ·)) hle his]
    _ = ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra s := by
      rw [ExteriorAlgebra.basis_apply_ofCard b rfl]

private theorem contractLeft_exteriorBasis (i : I) (s : Finset I) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i)
        (b.ExteriorAlgebra s) =
      if i ∈ s then
        (-1 : k) ^ (s.filter (· < i)).card • b.ExteriorAlgebra (s.erase i)
      else 0 := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
      rw [show b.ExteriorAlgebra (∅ : Finset I) = 1 by
        calc
          b.ExteriorAlgebra (∅ : Finset I) =
              ExteriorAlgebra.ιMulti_family k 0 b
                (Set.powersetCard.ofCard (by simp)) :=
            ExteriorAlgebra.basis_apply_ofCard b _
          _ = 1 := ExteriorAlgebra.ιMulti_zero_apply _]
      simp
  | insert a s ha ih =>
      rw [exteriorBasis_insert_min b a s ha,
        CliffordAlgebra.contractLeft_ι_mul]
      by_cases hai : a = i
      · subst a
        have his : i ∉ s := fun his => (ha i his).false
        have hfilter : s.filter (· < i) = ∅ := by
          ext j
          simp only [Finset.mem_filter]
          constructor
          · intro hj
            exact (not_lt_of_ge (ha j hj.1).le hj.2).elim
          · intro hj
            simp at hj
        rw [ih, if_neg his]
        simp [his, hfilter, Finset.filter_insert]
      · have hcoord : b.coord i (b a) = 0 := by
          simp [Module.Basis.coord_apply, Module.Basis.repr_self, hai]
        have hai_ne : i ≠ a := Ne.symm hai
        rw [hcoord, zero_smul, zero_sub, ih]
        by_cases his : i ∈ s
        · have hai' : a < i := ha i his
          have haerase : ∀ j ∈ s.erase i, a < j := by
            intro j hj
            exact ha j (Finset.mem_of_mem_erase hj)
          have has : a ∉ s := fun has => (ha a has).false
          have hafilter : a ∉ s.filter (· < i) := by simp [has]
          have herase : (insert a s).erase i = insert a (s.erase i) :=
            Finset.erase_insert_of_ne hai
          rw [if_pos his, mul_smul_comm,
            ← exteriorBasis_insert_min b a (s.erase i) haerase]
          simp [hai_ne, his, hai', hafilter, herase,
            Finset.filter_insert, pow_succ']
        · simp [hai_ne, his]

public theorem exterior_eq_scalar_of_forall_contractLeft_eq_zero
    [Fintype I]
    (b : Module.Basis I k V)
    (x : ExteriorAlgebra k V)
    (h : ∀ d : Module.Dual k V,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) d x = 0) :
    ∃ a : k, x = algebraMap k (ExteriorAlgebra k V) a := by
  classical
  let eb := Module.Basis.ExteriorAlgebra b
  let c := eb.repr x
  have hc (s : Finset I) (hs : s.Nonempty) : c s = 0 := by
    let i := s.min' hs
    let t := s.erase i
    have his : i ∈ s := s.min'_mem hs
    have hit : ∀ j ∈ t, i < j := by
      intro j hj
      exact s.min'_lt_of_mem_erase_min' hs hj
    have hzero := congrArg eb.repr (h (b.coord i))
    rw [map_zero] at hzero
    rw [← eb.sum_repr x] at hzero
    simp only [map_sum, map_smul] at hzero
    have hzero := congrArg (Finsupp.applyAddHom t) hzero
    simp only [map_sum, map_zero, Finsupp.applyAddHom_apply] at hzero
    simp only [eb, contractLeft_exteriorBasis b] at hzero
    have hrepr (r : Finset I) :
        (b.ExteriorAlgebra.repr
          (if i ∈ r then
            (-1 : k) ^ (r.filter (· < i)).card •
              b.ExteriorAlgebra (r.erase i)
          else 0)) t =
        if i ∈ r then
          (-1 : k) ^ (r.filter (· < i)).card •
            (b.ExteriorAlgebra.repr (b.ExteriorAlgebra (r.erase i))) t
        else 0 := by
      by_cases hir : i ∈ r
      · by_cases hrt : r.erase i = t
        · simp [hir, hrt]
        · simp [hir, hrt]
      · simp only [if_neg hir, map_zero, Finsupp.zero_apply]
    simp only [Finsupp.smul_apply] at hzero
    simp_rw [hrepr] at hzero
    simp only [Module.Basis.repr_self_apply] at hzero
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero] at hzero
    have hsum :
        (∑ r : Finset I,
          if i ∈ r then
            if r.erase i = t then
              (b.ExteriorAlgebra.repr x) r *
                (-1 : k) ^ (r.filter (· < i)).card
            else 0
          else 0) =
        (b.ExteriorAlgebra.repr x) s *
          (-1 : k) ^ (s.filter (· < i)).card := by
      calc
        _ = if i ∈ s then
              if s.erase i = t then
                (b.ExteriorAlgebra.repr x) s *
                  (-1 : k) ^ (s.filter (· < i)).card
              else 0
            else 0 := by
          apply Fintype.sum_eq_single s
          intro r hrs
          by_cases hir : i ∈ r
          · by_cases herase : r.erase i = t
            · exfalso
              apply hrs
              rw [← Finset.insert_erase hir, ← Finset.insert_erase his, herase]
            · simp [hir, herase]
          · simp [hir]
        _ = _ := by simp [his, t]
    rw [hsum] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero _ (by simp))
  refine ⟨c ∅, ?_⟩
  have hrepr_one : eb.repr (1 : ExteriorAlgebra k V) = Finsupp.single ∅ 1 := by
    rw [show (1 : ExteriorAlgebra k V) = eb ∅ by
      change (1 : ExteriorAlgebra k V) = b.ExteriorAlgebra ∅
      symm
      calc
        b.ExteriorAlgebra (∅ : Finset I) =
            ExteriorAlgebra.ιMulti_family k 0 b
              (Set.powersetCard.ofCard (by simp)) :=
          ExteriorAlgebra.basis_apply_ofCard b _
        _ = 1 := ExteriorAlgebra.ιMulti_zero_apply _]
    exact eb.repr_self ∅
  apply eb.repr.injective
  ext s
  by_cases hs : s.Nonempty
  · rw [hc s hs]
    rw [Algebra.algebraMap_eq_smul_one]
    rw [map_smul, hrepr_one]
    simp [hs.ne_empty]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    rw [Algebra.algebraMap_eq_smul_one]
    change (eb.repr x) ∅ = (eb.repr ((eb.repr x) ∅ • 1)) ∅
    rw [map_smul, hrepr_one]
    simp

end ExteriorBasis

variable [FiniteDimensional k V]

/-- An even element of a split Clifford algebra centralizing all vectors is a
scalar.  This is valid over every field, including characteristic two. -/
public theorem CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_ι
    (s : SplitQuadraticForm Q) (x : CliffordAlgebra Q)
    (hx : x ∈ CliffordAlgebra.even Q)
    (hcomm : ∀ v : V, Commute x (CliffordAlgebra.ι Q v)) :
    ∃ a : k, x = algebraMap k (CliffordAlgebra Q) a := by
  let e : CliffordAlgebra Q ≃ₗ[k] ExteriorAlgebra k V :=
    CliffordAlgebra.changeFormEquiv s.bilinear_toQuadraticMap
  have hpolar (v : V) :
      CliffordAlgebra.contractLeft (Q.polarBilin v) x = 0 := by
    rw [contractLeft_eq_commutator_of_mem_even x hx v, sub_eq_zero]
    exact (hcomm v).eq.symm
  have hcontract (d : Module.Dual k V) :
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) d (e x) = 0 := by
    obtain ⟨v, rfl⟩ := s.polarBilin_surjective d
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V))
      (Q.polarBilin v)
      (CliffordAlgebra.changeForm s.bilinear_toQuadraticMap x) = 0
    rw [← CliffordAlgebra.changeForm_contractLeft]
    rw [hpolar v, map_zero]
  obtain ⟨a, ha⟩ :=
    exterior_eq_scalar_of_forall_contractLeft_eq_zero
      (Module.finBasis k V) (e x) hcontract
  refine ⟨a, e.injective ?_⟩
  rw [ha]
  simp [e, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_algebraMap]

end Theory.AlgebraicGroup
