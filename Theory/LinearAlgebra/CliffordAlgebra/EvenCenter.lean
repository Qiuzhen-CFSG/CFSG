module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Tactic.NoncommRing

/-!
# Scalar center of the even Clifford algebra in odd dimension

For a finite-dimensional nondegenerate quadratic space over a field in which
two is invertible, this module proves that an even Clifford element commuting
with the whole even subalgebra is scalar when the dimension is odd.  The
argument is PBW-based: an orthogonal basis gives invertible Clifford vectors,
commutator identities convert centrality into anticommutation, and the odd
volume element forces the resulting anticommuting element to vanish.  The
change-of-form equivalence with the exterior algebra and its checked PBW basis
then reduce vanishing contractions to a scalar.

This is the direct Clifford/PBW proof used by the odd Spin-center calculation;
it does not invoke a Spin-center theorem.  The exterior contraction argument
follows the ordered-basis computation in the split Clifford centralizer layer.
-/

open CliffordAlgebra
open LinearMap (BilinForm)
open scoped BigOperators
universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {q : QuadraticForm k V}

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private theorem list_anti_general (t : CliffordAlgebra q) (l : List (CliffordAlgebra q))
    (hanti : ∀ z ∈ l, t * z = - z * t) :
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
private theorem list_prod_commute_of_mem {l : List V} (hpair : l.Pairwise q.IsOrtho)
    (a : V) (ha : a ∈ l) :
    ι q a * (l.map (ι q)).prod =
      (-1 : k) ^ (l.length - 1) • ((l.map (ι q)).prod * ι q a) := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    obtain rfl | ⟨hne, ha'⟩ := List.eq_or_ne_mem_of_mem ha
    · rw [List.map_cons, List.prod_cons]
      have hrest : ∀ c ∈ l, q.IsOrtho a c := by
        intro c hc
        exact (List.pairwise_cons.mp hpair).1 c hc
      have hanti := list_anti_general (q := q) (ι q a) (l.map (ι q)) (by
        intro z hz
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
        simpa only [neg_mul] using
          (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (hrest c hc)))
      calc
        ι q a * ((ι q a) * (l.map (ι q)).prod) =
            (ι q a * ι q a) * (l.map (ι q)).prod := by rw [mul_assoc]
        _ = algebraMap k _ (q a) * (l.map (ι q)).prod := by rw [ι_sq_scalar]
        _ = (-1 : k) ^ l.length •
              ((ι q a) * (l.map (ι q)).prod * ι q a) := by
          calc
            algebraMap k _ (q a) * (l.map (ι q)).prod =
                ((ι q a) * ι q a) * (l.map (ι q)).prod := by
                  rw [CliffordAlgebra.ι_sq_scalar]
            _ = (ι q a) * ((ι q a) * (l.map (ι q)).prod) := by rw [mul_assoc]
            _ = (ι q a) * ((-1 : k) ^ (l.map (ι q)).length •
                  ((l.map (ι q)).prod * ι q a)) := by rw [hanti]
            _ = (-1 : k) ^ l.length •
                  ((ι q a) * (l.map (ι q)).prod * ι q a) := by
                  rw [mul_smul_comm]
                  simp only [List.length_map, mul_assoc]
        _ = (-1 : k) ^ ((a :: l).length - 1) •
              ((ι q a) * (l.map (ι q)).prod * ι q a) := by simp
    · rw [List.map_cons, List.prod_cons]
      have hab : q.IsOrtho a b := (List.pairwise_cons.mp hpair).1 a ha' |>.symm
      calc
        ι q a * (ι q b * (l.map (ι q)).prod) =
            (ι q a * ι q b) * (l.map (ι q)).prod := by rw [mul_assoc]
        _ = (-(ι q b * ι q a)) * (l.map (ι q)).prod := by
          rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hab]
        _ = -((ι q b) * (ι q a * (l.map (ι q)).prod)) := by noncomm_ring
        _ = -(ι q b * ((-1 : k) ^ (l.length - 1) •
              ((l.map (ι q)).prod * ι q a))) := by
              rw [ih (List.pairwise_cons.mp hpair).2 ha']
        _ = (-1 : k) ^ ((b :: l).length - 1) •
              ((ι q b) * (l.map (ι q)).prod * ι q a) := by
              have hlen : 0 < l.length := (List.length_pos_iff.mpr (by
                intro hz
                subst hz
                simp at ha'))
              have hpow : (-1 : k) ^ l.length =
                  - ((-1 : k) ^ (l.length - 1)) := by
                have hEq : l.length = (l.length - 1) + 1 := by omega
                rw [hEq, pow_succ]
                simp
              have hcons : (b :: l).length - 1 = l.length := by simp
              rw [hcons, mul_smul_comm, ← neg_smul, hpow]
              simp only [mul_assoc]

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private theorem contractLeft_eq_commutator_of_mem_even
    (x : CliffordAlgebra q) (hx : x ∈ CliffordAlgebra.even q) (v : V) :
    CliffordAlgebra.contractLeft (q.polarBilin v) x =
      CliffordAlgebra.ι q v * x - x * CliffordAlgebra.ι q v := by
  change x ∈ CliffordAlgebra.evenOdd q 0 at hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap, Algebra.commutes]
  | add x y hx hy ihx ihy => simp only [map_add, mul_add, add_mul, ihx, ihy]; abel
  | ι_mul_ι_mul a b x hx ih =>
      simp only [mul_assoc]
      rw [CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, ih]
      simp only [QuadraticMap.polarBilin_apply_apply, Algebra.smul_def]
      have hva : algebraMap k (CliffordAlgebra q) (QuadraticMap.polar q v a) =
          CliffordAlgebra.ι q v * CliffordAlgebra.ι q a +
            CliffordAlgebra.ι q a * CliffordAlgebra.ι q v :=
        (CliffordAlgebra.ι_mul_ι_add_swap v a).symm
      have hvb : algebraMap k (CliffordAlgebra q) (QuadraticMap.polar q v b) =
          CliffordAlgebra.ι q v * CliffordAlgebra.ι q b +
            CliffordAlgebra.ι q b * CliffordAlgebra.ι q v :=
        (CliffordAlgebra.ι_mul_ι_add_swap v b).symm
      rw [hva, hvb]
      noncomm_ring

section ExteriorBasis
variable {I : Type*} [LinearOrder I] (b : Module.Basis I k V)

omit [Invertible (2 : k)] [FiniteDimensional k V] in
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

omit [Invertible (2 : k)] [FiniteDimensional k V] in
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
      · simp [Set.powersetCard.ofFinEmbEquiv_symm_apply,
          Finset.orderEmbOfFin_apply, Finset.sort_insert (r := (· ≤ ·)) hle his]
      · congr 1
        ext j
        simp [Matrix.vecTail, Set.powersetCard.ofFinEmbEquiv_symm_apply,
          Finset.orderEmbOfFin_apply,
          Finset.sort_insert (r := (· ≤ ·)) hle his]
    _ = ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra s := by
      rw [ExteriorAlgebra.basis_apply_ofCard b rfl]

omit [Invertible (2 : k)] [FiniteDimensional k V] in
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

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private theorem exterior_eq_scalar_of_forall_contractLeft_eq_zero_odd
    (b : Module.Basis I k V) (x : ExteriorAlgebra k V)
    [Fintype I]
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

private theorem scalar_of_commute_vectors
    (hq : q.Nondegenerate) (x : CliffordAlgebra q)
    (hx : x ∈ CliffordAlgebra.even q)
    (hcomm : ∀ v : V, Commute x (CliffordAlgebra.ι q v)) :
    ∃ a : k, x = algebraMap k (CliffordAlgebra q) a := by
  let e : CliffordAlgebra q ≃ₗ[k] ExteriorAlgebra k V :=
    CliffordAlgebra.equivExterior q
  have hpolar_surj : Function.Surjective q.polarBilin := by
    have hsep : (q.polarBilin).SeparatingLeft :=
      ((QuadraticMap.nondegenerate_polar_iff).mpr hq).1
    have hinj : Function.Injective q.polarBilin := by
      apply (LinearMap.ker_eq_bot.mp
        ((LinearMap.separatingLeft_iff_ker_eq_bot).mp hsep))
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := k) (V := V)).symm).mp hinj
  have hpolar (v : V) :
      CliffordAlgebra.contractLeft (q.polarBilin v) x = 0 := by
    rw [contractLeft_eq_commutator_of_mem_even x hx v, sub_eq_zero]
    exact (hcomm v).eq.symm
  have hcontract (d : Module.Dual k V) :
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) d (e x) = 0 := by
    obtain ⟨v, rfl⟩ := hpolar_surj d
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V))
      (q.polarBilin v)
      (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof x) = 0
    rw [← CliffordAlgebra.changeForm_contractLeft]
    rw [hpolar v, map_zero]
  obtain ⟨a, ha⟩ :=
    exterior_eq_scalar_of_forall_contractLeft_eq_zero_odd
      (Module.finBasis k V) (e x) hcontract
  refine ⟨a, e.injective ?_⟩
  rw [ha]
  simp [e]

private theorem odd_ne_zero {n : Nat} (h : Odd n) : n ≠ 0 := by
  intro hn
  subst hn
  rcases h with ⟨m, hm⟩
  omega

private theorem odd_sub_one_even {n : Nat} (h : Odd n) : Even (n - 1) := by
  rcases h with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  omega

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private theorem list_anti_general_odd (t : CliffordAlgebra q)
    (l : List (CliffordAlgebra q))
    (hanti : ∀ z ∈ l, t * z = - z * t) :
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

public theorem CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_even
    (hq : q.Nondegenerate) (hodd : Odd (Module.finrank k V))
    (x : CliffordAlgebra q) (hx : x ∈ CliffordAlgebra.even q)
    (hcomm : ∀ y : CliffordAlgebra q,
      y ∈ CliffordAlgebra.even q → x * y = y * x) :
    ∃ a : k, x = algebraMap k (CliffordAlgebra q) a := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
      (B := QuadraticMap.associated q) (QuadraticForm.associated_isSymm k q)
  have hsep : (QuadraticMap.associated q).SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff).mpr hq).1
  have hbpair : ∀ i j, i ≠ j → (QuadraticMap.associated q) (b i) (b j) = 0 := by
    intro i j hij
    exact hb hij
  have hbq : ∀ i, q (b i) ≠ 0 := by
    intro i
    have hi := hb.not_isOrtho_basis_self_of_separatingLeft hsep i
    simpa [QuadraticMap.associated_eq_self_apply] using hi
  let e : Fin (Module.finrank k V) → CliffordAlgebra q := fun i => ι q (b i)
  have heq (i j : Fin (Module.finrank k V)) (hij : i ≠ j) :
      e i * e j = - e j * e i := by
    simpa [e] using CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (QuadraticMap.associated_isOrtho.mp (hbpair i j hij))
  have heunit (i : Fin (Module.finrank k V)) : IsUnit (e i) := by
    apply CliffordAlgebra.isUnit_ι_of_isUnit
    exact isUnit_iff_ne_zero.mpr (hbq i)
  letI (i : Fin (Module.finrank k V)) : Invertible (q (b i)) :=
    invertibleOfNonzero (hbq i)
  letI (i : Fin (Module.finrank k V)) : Invertible (e i) := by
    dsimp [e]
    exact CliffordAlgebra.invertibleιOfInvertible q (b i)
  let c : Fin (Module.finrank k V) → CliffordAlgebra q :=
    fun i => x * e i - e i * x
  have hcodd (i : Fin (Module.finrank k V)) : c i ∈ CliffordAlgebra.evenOdd q 1 := by
    apply Submodule.sub_mem
    · exact (zero_add (1 : ZMod 2)) ▸ SetLike.mul_mem_graded hx
        (ι_mem_evenOdd_one q (b i))
    · exact (add_zero (1 : ZMod 2)) ▸ SetLike.mul_mem_graded
        (ι_mem_evenOdd_one q (b i)) hx
  have hrel (i j : Fin (Module.finrank k V)) :
      c i * e j + e i * c j = 0 := by
    have hmem : e i * e j ∈ CliffordAlgebra.even q := by
      change e i * e j ∈ CliffordAlgebra.evenOdd q 0
      exact ι_mul_ι_mem_evenOdd_zero q (b i) (b j)
    have hh := hcomm (e i * e j) hmem
    calc
      c i * e j + e i * c j = x * (e i * e j) - (e i * e j) * x := by
        dsimp [c]
        noncomm_ring
      _ = 0 := by rw [hh]; simp
  let i0 : Fin (Module.finrank k V) :=
    ⟨0, Nat.pos_of_ne_zero (odd_ne_zero hodd)⟩
  let t : CliffordAlgebra q := ⅟ (e i0) * c i0
  have ht_even : t ∈ CliffordAlgebra.evenOdd q 0 := by
    dsimp [t]
    have hi0 : ⅟ (e i0) ∈ CliffordAlgebra.evenOdd q 1 := by
      rw [show ⅟ (e i0) = ι q (⅟(q (b i0)) • b i0) by
        dsimp [e]
        rw [CliffordAlgebra.invOf_ι]]
      exact ι_mem_evenOdd_one q _
    have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    exact h11 ▸ SetLike.mul_mem_graded hi0 (hcodd i0)
  have hc0anti : c i0 * ⅟ (e i0) = -t := by
    have h := hrel i0 i0
    have h' : c i0 * e i0 = - e i0 * c i0 := by
      simpa [add_eq_zero_iff_eq_neg] using h
    apply (isUnit_of_invertible (e i0)).mul_right_cancel
    calc
      (c i0 * ⅟ (e i0)) * e i0 = c i0 := by
        rw [mul_assoc, invOf_mul_self, mul_one]
      _ = (-t) * e i0 := by
        dsimp [t]
        rw [neg_mul, mul_assoc, h']
        simp
  have hce (i : Fin (Module.finrank k V)) : c i = e i * t := by
    have h := hrel i i0
    have hh : c i * e i0 = - e i * c i0 := by
      simpa [add_eq_zero_iff_eq_neg] using h
    calc
      c i = (c i * e i0) * ⅟ (e i0) := by rw [mul_assoc, mul_invOf_self, mul_one]
      _ = (- e i * c i0) * ⅟ (e i0) := by rw [hh]
      _ = - e i * (c i0 * ⅟ (e i0)) := by noncomm_ring
      _ = e i * t := by rw [hc0anti]; simp
  have htanti (i : Fin (Module.finrank k V)) : t * e i = - e i * t := by
    have h := hrel i0 i
    have hh' := congrArg (fun z => ⅟ (e i0) * z) h
    have hh'' : (⅟ (e i0) * c i0) * e i + c i = 0 := by
      simpa [mul_add, mul_assoc, invOf_mul_self, one_mul] using hh'
    calc
      t * e i = - c i := by
        dsimp [t]
        simpa [add_eq_zero_iff_eq_neg] using hh''
      _ = - e i * t := by rw [hce i, neg_mul]
  have htbasis (v : V) : t * ι q v = - ι q v * t := by
    rw [← b.sum_repr v]
    simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
    have hanti' (i : Fin _) : t * ι q (b i) = -ι q (b i) * t := by
      simpa [e] using htanti i
    have hsum_mul :
        (∑ i, (b.repr v) i • ι q (b i)) * t =
          ∑ i, (b.repr v) i • (ι q (b i) * t) := by
      simp [Algebra.smul_def, Finset.sum_mul, mul_assoc]
    calc
      (∑ i, (b.repr v) i • (t * ι q (b i))) =
          ∑ i, (b.repr v) i • (-(ι q (b i) * t)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hanti' i, neg_mul]
      _ = - ∑ i, (b.repr v) i • (ι q (b i) * t) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_neg]
      _ = -((∑ i, (b.repr v) i • ι q (b i)) * t) := by
            exact congrArg Neg.neg hsum_mul.symm
      _ = (-(∑ i, (b.repr v) i • ι q (b i))) * t := by rw [neg_mul]
  let l : List V := List.ofFn (fun i => b i)
  have hpair : l.Pairwise q.IsOrtho := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact QuadraticMap.associated_isOrtho.mp (hbpair i j hij.ne)
  have hvolanti : ∀ i : Fin _, ι q (b i) * (l.map (ι q)).prod =
      (-1 : k) ^ (l.length - 1) • ((l.map (ι q)).prod * ι q (b i)) := by
    intro i
    exact list_prod_commute_of_mem hpair (b i) (by
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩)
  have hvolcentral (v : V) : ι q v * (l.map (ι q)).prod =
      (l.map (ι q)).prod * ι q v := by
    rw [← b.sum_repr v]
    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc,
      mul_smul_comm]
    have hs : (-1 : k) ^ (l.length - 1) = 1 := by
      apply Even.neg_one_pow
      simpa [l] using odd_sub_one_even hodd
    simp_rw [hvolanti, hs, one_smul]
  have hvolt : t * (l.map (ι q)).prod =
      (-1 : k) ^ l.length • ((l.map (ι q)).prod * t) :=
    (by
      simpa only [List.length_map] using
        (list_anti_general_odd t (l.map (ι q)) (by
      intro z hz
      obtain ⟨v, hv, hEq⟩ := List.mem_map.mp hz
      rw [← hEq]
      exact htbasis v)))
  have hsign : (-1 : k) ^ l.length = -1 := by simpa [l] using hodd.neg_one_pow
  have htzero : t = 0 := by
    have hz : t * (l.map (ι q)).prod = - (l.map (ι q)).prod * t := by
      rw [hvolt, hsign]
      simp
    have hvol_comm_even (y : CliffordAlgebra q) (hy : y ∈ CliffordAlgebra.even q) :
        (l.map (ι q)).prod * y = y * (l.map (ι q)).prod := by
      change y ∈ CliffordAlgebra.evenOdd q 0 at hy
      induction y, hy using CliffordAlgebra.even_induction with
      | algebraMap r => simp [Algebra.commutes]
      | add y z hy hz ihy ihz => rw [mul_add, add_mul, ihy, ihz]
      | ι_mul_ι_mul a b y hy ih =>
          have ha : (l.map (ι q)).prod * ι q a = ι q a * (l.map (ι q)).prod :=
            (hvolcentral a).symm
          have hb : (l.map (ι q)).prod * ι q b = ι q b * (l.map (ι q)).prod :=
            (hvolcentral b).symm
          calc
              (l.map (ι q)).prod * ((ι q a * ι q b) * y) =
                  (((l.map (ι q)).prod * ι q a) * ι q b) * y := by simp only [mul_assoc]
              _ = ((ι q a * (l.map (ι q)).prod) * ι q b) * y := by rw [ha]
              _ = (ι q a * ((l.map (ι q)).prod * ι q b)) * y := by simp only [mul_assoc]
              _ = (ι q a * (ι q b * (l.map (ι q)).prod)) * y := by rw [hb]
              _ = ι q a * (ι q b * ((l.map (ι q)).prod * y)) := by simp only [mul_assoc]
              _ = ι q a * (ι q b * (y * (l.map (ι q)).prod)) := by rw [ih]
              _ = ((ι q a * ι q b) * y) * (l.map (ι q)).prod := by simp only [mul_assoc]
    have hz' : t * (l.map (ι q)).prod = (l.map (ι q)).prod * t := by
      exact (hvol_comm_even t ht_even).symm
    have hsum : (2 : k) • (t * (l.map (ι q)).prod) = 0 := by
      calc
        (2 : k) • (t * (l.map (ι q)).prod) =
            t * (l.map (ι q)).prod + t * (l.map (ι q)).prod := by
              simp [two_smul]
        _ = (-(l.map (ι q)).prod * t) + (l.map (ι q)).prod * t := by
              calc
                _ = -(l.map (ι q)).prod * t + t * (l.map (ι q)).prod := by rw [hz]
                _ = _ := by rw [hz']
        _ = 0 := by rw [neg_mul]; exact neg_add_cancel _
    have hzprod : t * (l.map (ι q)).prod = 0 := by
      have htwo : (2 : k) ≠ 0 := by exact (Invertible.ne_zero (2 : k))
      exact (smul_eq_zero.mp hsum).resolve_left htwo
    have hprodunit : IsUnit ((l.map (ι q)).prod) := by
      exact List.prod_isUnit fun z hz => by
        obtain ⟨v, hv, hEq⟩ := List.mem_map.mp hz
        rw [← hEq]
        have hv' : v ∈ List.ofFn (fun i => b i) := by simpa [l] using hv
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv'
        exact heunit i
    apply hprodunit.mul_right_cancel
    simpa using hzprod
  apply scalar_of_commute_vectors hq x hx
  intro v
  have hcvzero (i : Fin _) : c i = 0 := by rw [hce i, htzero, mul_zero]
  change x * ι q v = ι q v * x
  apply sub_eq_zero.mp
  rw [← b.sum_repr v]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc,
    mul_smul_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← smul_sub]
  simpa only [c, smul_zero] using
    congrArg (fun z => (b.repr v) i • z) (hcvzero i)

end Theory.AlgebraicGroup
