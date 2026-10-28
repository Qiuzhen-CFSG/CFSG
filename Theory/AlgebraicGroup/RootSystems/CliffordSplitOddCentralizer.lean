module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitCentralizer
public import Theory.LinearAlgebra.CliffordAlgebra.OddVolume
public import Mathlib.Tactic.NoncommRing

/-!
# Odd centralizers in split Clifford algebras

Let `Q` be a finite-dimensional split quadratic form of positive hyperbolic
rank over an arbitrary field.  This module proves that an odd Clifford element
which commutes with every embedded vector is zero.  In particular, the full
Clifford centralizer has no odd unit.  The result is the lower-layer parity
input used by the split Dickson-invariant and even normalizer constructions.

The proof deliberately separates characteristic two.  When `2 = 0`, the odd
involute identity turns contraction by the polar form into twice a commuting
product, hence into zero.  Split polar perfectness and the change-of-form
equivalence then reduce to the exterior PBW basis theorem: vanishing of every
left contraction leaves only the scalar monomial.  Since the even and odd PBW
summands are complementary, that scalar odd element is zero.

When `2 ≠ 0`, an orthogonal basis for the nondegenerate form gives a Clifford
volume unit.  Splitness identifies the dimension with twice the hyperbolic
rank, so moving a basis vector through the volume contributes a minus sign.
Induction on Mathlib's odd Clifford generators extends this anticommutation to
the given element.  Centrality supplies the opposite equality, cancellation
of `2`, and then cancellation of the volume unit.  Thus no global
`Invertible (2 : k)` hypothesis is imposed, and the changeForm/PBW branch
covers characteristic two rather than excluding it.  This is the standard
even-dimensional Clifford-center argument, organized here around the explicit
split witness from `CliffordSplitPBW`.
-/

open CliffordAlgebra

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

omit [FiniteDimensional k V] in
private theorem contractLeft_eq_supercommutator
    (x : CliffordAlgebra Q) (v : V) :
    CliffordAlgebra.contractLeft (Q.polarBilin v) x =
      CliffordAlgebra.ι Q v * x -
        CliffordAlgebra.involute x * CliffordAlgebra.ι Q v := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [CliffordAlgebra.contractLeft_algebraMap,
        CliffordAlgebra.involute, Algebra.commutes]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, add_mul, mul_add]
      abel
  | ι_mul x a ih =>
      rw [CliffordAlgebra.contractLeft_ι_mul, ih,
        map_mul, CliffordAlgebra.involute_ι]
      simp only [mul_assoc]
      have hv : algebraMap k (CliffordAlgebra Q) (QuadraticMap.polar Q v a) =
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a +
            CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q v :=
        (CliffordAlgebra.ι_mul_ι_add_swap v a).symm
      rw [QuadraticMap.polarBilin_apply_apply, Algebra.smul_def, hv]
      noncomm_ring

private theorem eq_algebraMap_of_mem_odd_of_commute_ι_of_two_eq_zero
    (s : SplitQuadraticForm Q) (x : CliffordAlgebra Q)
    (hx : x ∈ CliffordAlgebra.evenOdd Q 1)
    (hcomm : ∀ v : V, Commute x (CliffordAlgebra.ι Q v))
    (h2 : (2 : k) = 0) :
    ∃ a : k, x = algebraMap k (CliffordAlgebra Q) a := by
  let e : CliffordAlgebra Q ≃ₗ[k] ExteriorAlgebra k V :=
    CliffordAlgebra.changeFormEquiv s.bilinear_toQuadraticMap
  have hpolar (v : V) :
      CliffordAlgebra.contractLeft (Q.polarBilin v) x = 0 := by
    rw [contractLeft_eq_supercommutator]
    rw [CliffordAlgebra.involute_eq_of_mem_odd hx]
    rw [(hcomm v).eq.symm]
    rw [neg_mul, sub_neg_eq_add,
      ← two_smul k (x * CliffordAlgebra.ι Q v), h2, zero_smul]
  have hcontract : ∀ d : Module.Dual k V,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) d (e x) = 0 := by
    intro d
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
  simpa [e, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_algebraMap] using ha

private theorem eq_zero_of_mem_odd_of_commute_ι_of_two_eq_zero
    (s : SplitQuadraticForm Q) (x : CliffordAlgebra Q)
    (hx : x ∈ CliffordAlgebra.evenOdd Q 1)
    (hcomm : ∀ v : V, Commute x (CliffordAlgebra.ι Q v))
    (h2 : (2 : k) = 0) : x = 0 := by
  obtain ⟨a, ha⟩ :=
    eq_algebraMap_of_mem_odd_of_commute_ι_of_two_eq_zero s x hx hcomm h2
  have heven : x ∈ CliffordAlgebra.even Q := by
    rw [ha]
    exact SetLike.algebraMap_mem_graded _ _
  change x ∈ CliffordAlgebra.evenOdd Q 0 at heven
  have hbot : x ∈ (⊥ : Submodule k (CliffordAlgebra Q)) :=
    (CliffordAlgebra.evenOdd_isCompl Q).disjoint.le_bot ⟨heven, hx⟩
  simpa using hbot

omit [FiniteDimensional k V] in
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

omit [FiniteDimensional k V] in
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

omit [FiniteDimensional k V] in
private lemma cliffordVolumeUnit_anticommute_ι
    [Invertible (2 : k)]
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hborth : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
    (hbq : ∀ i, Q (b i) ≠ 0)
    (heven : Even (Module.finrank k V))
    (hpos : 0 < Module.finrank k V) (v : V) :
    (cliffordVolumeUnit b hbq : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
      -(CliffordAlgebra.ι Q v *
        (cliffordVolumeUnit b hbq : CliffordAlgebra Q)) := by
  let l : List V := List.ofFn fun i => b i
  have hpair : l.Pairwise Q.IsOrtho := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hborth i j hij.ne
  have hbmove (i : Fin (Module.finrank k V)) :
      CliffordAlgebra.ι Q (b i) *
          (l.map (CliffordAlgebra.ι Q)).prod =
        -((l.map (CliffordAlgebra.ι Q)).prod *
          CliffordAlgebra.ι Q (b i)) := by
    rw [iota_mul_iotaList_prod_of_mem hpair (b i) (by
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩)]
    have hs : (-1 : k) ^ (l.length - 1) = -1 := by
      apply Odd.neg_one_pow
      apply Nat.Even.sub_odd (by simpa [l] using Nat.succ_le_iff.mpr hpos)
        (by simpa [l] using heven)
      exact odd_one
    rw [hs, neg_one_smul]
  have hbanti (i : Fin (Module.finrank k V)) :
      (l.map (CliffordAlgebra.ι Q)).prod * CliffordAlgebra.ι Q (b i) =
        -(CliffordAlgebra.ι Q (b i) *
          (l.map (CliffordAlgebra.ι Q)).prod) := by
    have h := congrArg Neg.neg (hbmove i)
    simpa using h.symm
  rw [cliffordVolumeUnit_coe]
  change (List.ofFn fun i => CliffordAlgebra.ι Q (b i)).prod *
      CliffordAlgebra.ι Q v =
    -(CliffordAlgebra.ι Q v *
      (List.ofFn fun i => CliffordAlgebra.ι Q (b i)).prod)
  rw [show (List.ofFn fun i => CliffordAlgebra.ι Q (b i)) =
      l.map (CliffordAlgebra.ι Q) by simp [l, List.ofFn_eq_map]]
  rw [← b.sum_repr v]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul,
    smul_mul_assoc, mul_smul_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [smul_neg] using
    congrArg (fun z => (b.repr v) i • z) (hbanti i)

omit [FiniteDimensional k V] in
private lemma volume_anticommute_odd
    (omega : CliffordAlgebra Q)
    (homega : ∀ v : V, omega * CliffordAlgebra.ι Q v =
      -(CliffordAlgebra.ι Q v * omega))
    (x : CliffordAlgebra Q) (hx : x ∈ CliffordAlgebra.evenOdd Q 1) :
    omega * x = -(x * omega) := by
  induction x, hx using CliffordAlgebra.odd_induction with
  | ι v => exact homega v
  | add x y hx hy ihx ihy => rw [mul_add, add_mul, ihx, ihy, neg_add]
  | ι_mul_ι_mul a b x hx ih =>
      calc
        omega * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * x) =
            (omega * CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q b * x := by
              simp only [mul_assoc]
        _ = (-(CliffordAlgebra.ι Q a * omega)) *
            CliffordAlgebra.ι Q b * x := by rw [homega a]
        _ = -(CliffordAlgebra.ι Q a *
            (omega * CliffordAlgebra.ι Q b) * x) := by noncomm_ring
        _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
            (omega * x) := by rw [homega b]; noncomm_ring
        _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
            (-(x * omega)) := by rw [ih]
        _ = -(CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * x * omega) := by
              noncomm_ring

private theorem eq_zero_of_mem_odd_of_commute_ι_of_two_ne_zero
    (hQ : Q.Nondegenerate) (heven : Even (Module.finrank k V))
    (hpos : 0 < Module.finrank k V) (x : CliffordAlgebra Q)
    (hx : x ∈ CliffordAlgebra.evenOdd Q 1)
    (hcomm : ∀ v : V, Commute x (CliffordAlgebra.ι Q v))
    (h2 : (2 : k) ≠ 0) : x = 0 := by
  let _ : Invertible (2 : k) := invertibleOfNonzero h2
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
  let omega : (CliffordAlgebra Q)ˣ := cliffordVolumeUnit b hbq
  have homega (v : V) :
      (omega : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
        -(CliffordAlgebra.ι Q v * (omega : CliffordAlgebra Q)) :=
    cliffordVolumeUnit_anticommute_ι b hborth hbq heven hpos v
  have hxomega : Commute x (omega : CliffordAlgebra Q) := by
    rw [cliffordVolumeUnit_coe]
    apply Commute.list_prod_right
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hcomm (b i)
  have hanti := volume_anticommute_odd (omega : CliffordAlgebra Q) homega x hx
  have hneg : x * (omega : CliffordAlgebra Q) =
      -(x * (omega : CliffordAlgebra Q)) := by
    calc
      x * (omega : CliffordAlgebra Q) =
          (omega : CliffordAlgebra Q) * x := hxomega.eq
      _ = -(x * (omega : CliffordAlgebra Q)) := hanti
  have hzero : x * (omega : CliffordAlgebra Q) = 0 := by
    have hadd := eq_neg_iff_add_eq_zero.mp hneg
    have hsmul : (2 : k) • (x * (omega : CliffordAlgebra Q)) = 0 := by
      simpa [two_smul] using hadd
    exact (smul_eq_zero.mp hsmul).resolve_left h2
  have hcancel := congrArg
    (fun z : CliffordAlgebra Q => z * (↑(omega⁻¹) : CliffordAlgebra Q)) hzero
  simpa [mul_assoc] using hcancel

private theorem split_finrank_eq (s : SplitQuadraticForm Q) :
    Module.finrank k V = 2 * s.rank := by
  rw [s.isometry.toLinearEquiv.finrank_eq]
  simp [HyperbolicSpace, Module.finrank_prod]
  omega

/-- An odd element of a positive-rank split Clifford algebra that commutes with
every embedded vector is zero.  The statement is characteristic-free. -/
public theorem CliffordAlgebra.eq_zero_of_mem_odd_of_commute_ι
    (s : SplitQuadraticForm Q) (hpos : 0 < s.rank)
    (x : CliffordAlgebra Q) (hx : x ∈ CliffordAlgebra.evenOdd Q 1)
    (hcomm : ∀ v : V, Commute x (CliffordAlgebra.ι Q v)) : x = 0 := by
  by_cases h2 : (2 : k) = 0
  · exact eq_zero_of_mem_odd_of_commute_ι_of_two_eq_zero s x hx hcomm h2
  · apply eq_zero_of_mem_odd_of_commute_ι_of_two_ne_zero s.nondegenerate
      (by rw [split_finrank_eq s]; exact even_two_mul s.rank)
      (by rw [split_finrank_eq s]; omega)
      x hx hcomm h2

end Theory.AlgebraicGroup
