module
public import Theory.Representation.FixedPointPermutation
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry

/-!
# The Suzuki ovoid permutation module

The highest vector of the full Frobenius tensor is fixed by the root group
and its torus: its weight is q−1. The resulting ovoid permutation map is
nonzero on augmentation, hence surjective onto the irreducible tensor.
Both spaces have dimension q², so this is an actual intertwining equivalence.
The odd number q²+1 of ovoid points splits constants, giving 1 ⊕ St and
semisimplicity over every extension of the defining field.

Source: Suzuki's rank-one Bruhat action and the native Frobenius tensor
classification; application to Aschbacher–Smith 13.6.27, printed p.934.
-/

@[expose] public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

private theorem full_weight' (m : ℕ) :
    supportWeight (Finset.univ : Support m) = 2 ^ (2 * m + 1) - 1 := by
  have h : ∀ n : ℕ, (∑ i : Fin n, 2 ^ i.val) + 1 = 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
      rw [← Finset.sum_mul]
      omega
  have hh := h (2*m+1)
  simpa [supportWeight] using (show (∑ i : Fin (2*m+1), 2^i.val) = 2^(2*m+1)-1 by omega)

theorem tensorHighestVector_full_fixed_borel (m : ℕ) (K : Type*) [Field K]
    [Algebra (F m) K] (g : SuzukiMatrixGroup m) (hg : g ∈ SuzukiBorelSubgroup m) :
    tensorRep m K Finset.univ g (tensorHighestVector m K Finset.univ) =
      tensorHighestVector m K Finset.univ := by
  let R := tensorRep m K Finset.univ
  let v := tensorHighestVector m K Finset.univ
  let fix : Subgroup (SuzukiMatrixGroup m) := {
    carrier := {g | R g v = v}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change R a v = v at ha
      change R b v = v at hb
      change R (a*b) v = v
      rw [map_mul, Module.End.mul_apply, hb, ha]
    inv_mem' := by
      intro a ha
      change R a v = v at ha
      change R a⁻¹ v = v
      have hh := congrArg (R a⁻¹) ha
      simpa only [R.inv_self_apply] using hh.symm }
  change g ∈ fix
  apply (show SuzukiBorelSubgroup m ≤ fix from ?_) hg
  rw [suzukiBorelSubgroup_eq_sup]
  refine sup_le (fun a ha => tensorHighestVector_fixed_root m K Finset.univ a ha) ?_
  intro a ha
  obtain ⟨t,ht⟩ := (mem_suzukiSplitTorus_iff m a).mp ha
  have he : a = highestTorus m t := Subtype.ext ht
  subst a
  change tensorRep m K Finset.univ (highestTorus m t) _ = _
  rw [tensorHighestVector_torus, full_weight']
  have ht : t.val ^ (2^(2*m+1)-1) = 1 := by
    have hh : t ^ Nat.card (F m)ˣ = 1 := pow_card_eq_one'
    rw [Nat.card_units, GaloisField.card 2 (2*m+1) (by omega)] at hh
    exact congrArg Units.val hh
  rw [mul_comm (1 + 2^m), pow_mul, ← map_pow, ht, map_one, one_pow, one_smul]

local instance (m : ℕ) : Fintype (SuzukiOvoid m) := Fintype.ofFinite _

theorem full_tensor_finrank (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K] :
    Module.finrank K (TensorSpace m K Finset.univ) = (2^(2*m+1))^2 := by
  rw [finrank_tensorSpace, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm (2*m+1) 2, pow_mul]
  rfl

theorem highest_full_moved {m : ℕ} (hm : 1 ≤ m) (K : Type*) [Field K] [Algebra (F m) K] :
    ∃ g, tensorRep m K Finset.univ g (tensorHighestVector m K Finset.univ) ≠
      tensorHighestVector m K Finset.univ := by
  by_contra! hh
  have hs := tensorHighestVector_orbit_span (K := K) hm Finset.univ
  have hr : (Set.range fun g : SuzukiMatrixGroup m =>
      tensorRep m K Finset.univ g (tensorHighestVector m K Finset.univ)) =
      {tensorHighestVector m K Finset.univ} := by
    ext w
    constructor
    · rintro ⟨g,rfl⟩
      exact hh g
    · rintro rfl
      exact ⟨1, by simp⟩
  rw [hr] at hs
  have hd := finrank_span_singleton (K := K) (tensorHighestVector_ne_zero m K Finset.univ)
  rw [hs, finrank_top, full_tensor_finrank] at hd
  have hp : 2 ≤ 2^(2*m+1) := Nat.le_pow (by omega)
  nlinarith

/-- The literal ovoid augmentation action is the full Suzuki tensor. -/
theorem ovoid_augmentation_equiv_full {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (F m) K] :
    Nonempty ((FixedPointPermutation.core (K := K) (G := SuzukiMatrixGroup m)
      (Ω := SuzukiOvoid m)).toRepresentation.Equiv (tensorRep m K Finset.univ)) := by
  let x := suzukiOvoidInfinity m
  let R := tensorRep m K Finset.univ
  let v := tensorHighestVector m K Finset.univ
  have hv : ∀ g : SuzukiMatrixGroup m, g • x = x → R g v = v := by
    intro g hg
    apply tensorHighestVector_full_fixed_borel
    rw [suzukiBorelSubgroup_eq_stabilizer m (by omega), MulAction.mem_stabilizer_iff]
    exact hg
  let f := FixedPointPermutation.coreOrbitMap x R v hv
  have hn : f ≠ 0 := FixedPointPermutation.coreOrbitMap_ne_zero x R v hv
    (highest_full_moved hm K)
  let : R.IsIrreducible := tensorRep_irreducible hm Finset.univ
  have hs : Function.Surjective f := (IsIrreducible.surjective_or_eq_zero f).resolve_right hn
  have hd : Module.finrank K (FixedPointPermutation.core (K := K)
      (G := SuzukiMatrixGroup m) (Ω := SuzukiOvoid m)).toSubmodule =
      Module.finrank K (TensorSpace m K Finset.univ) := by
    have hh := FixedPointPermutation.finrank_core (K := K) (G := SuzukiMatrixGroup m) x
    rw [← Nat.card_eq_fintype_card, suzukiOvoid_card] at hh
    rw [full_tensor_finrank]
    omega
  exact ⟨f.ofBijective ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem ovoid_augmentation_irreducible {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (F m) K] :
    (FixedPointPermutation.core (K := K) (G := SuzukiMatrixGroup m)
      (Ω := SuzukiOvoid m)).toRepresentation.IsIrreducible := by
  obtain ⟨e⟩ := ovoid_augmentation_equiv_full hm K
  let := tensorRep_irreducible (K := K) hm Finset.univ
  let er : (FixedPointPermutation.core (K := K) (G := SuzukiMatrixGroup m)
      (Ω := SuzukiOvoid m)).toRepresentation ≃ₗ tensorRep m K Finset.univ :=
    ⟨e.toLinearEquiv,e.isIntertwining'⟩
  exact er.irreducible_of_euqiv inferInstance

theorem ovoid_card_cast {m : ℕ} (K : Type*) [Field K] [Algebra (F m) K] :
    (Fintype.card (SuzukiOvoid m) : K) = 1 := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (F m) K).injective 2
  rw [← Nat.card_eq_fintype_card, suzukiOvoid_card]
  have hz : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, hz]
  simp

/-- The full ovoid permutation module is semisimple in characteristic two. -/
theorem ovoid_permutation_semisimple {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (F m) K] :
    IsSemisimpleModule (MonoidAlgebra K (SuzukiMatrixGroup m))
      (FixedPointPermutation.action (K := K) (G := SuzukiMatrixGroup m)
        (Ω := SuzukiOvoid m)).asModule :=
  FixedPointPermutation.semisimple_of_core_irreducible
    (by rw [ovoid_card_cast]; exact one_ne_zero) (ovoid_augmentation_irreducible hm K)

/-- The concrete ovoid action splits as the trivial line plus the full tensor. -/
theorem ovoid_permutation_equiv_trivial_prod_full {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (F m) K] :
    Nonempty (((trivial K (SuzukiMatrixGroup m) K).prod (tensorRep m K Finset.univ)).Equiv
      (FixedPointPermutation.action (K := K) (G := SuzukiMatrixGroup m) (Ω := SuzukiOvoid m))) := by
  obtain ⟨e⟩ := ovoid_augmentation_equiv_full hm K
  let p : ((trivial K (SuzukiMatrixGroup m) K).prod (tensorRep m K Finset.univ)).Equiv
      ((trivial K (SuzukiMatrixGroup m) K).prod
        (FixedPointPermutation.core (K := K) (G := SuzukiMatrixGroup m)
          (Ω := SuzukiOvoid m)).toRepresentation) :=
    .mk ((LinearEquiv.refl K K).prodCongr e.symm.toLinearEquiv) (by
      intro g
      apply LinearMap.ext
      rintro ⟨c,v⟩
      apply Prod.ext
      · rfl
      · exact LinearMap.congr_fun (e.symm.isIntertwining' g) v)
  have hc : (Fintype.card (SuzukiOvoid m) : K) ≠ 0 := by rw [ovoid_card_cast]; exact one_ne_zero
  let s := (FixedPointPermutation.splittingMap (K := K) (G := SuzukiMatrixGroup m)
    (Ω := SuzukiOvoid m)).ofBijective ⟨FixedPointPermutation.splittingMap_injective hc,
      FixedPointPermutation.splittingMap_surjective hc⟩
  exact ⟨p.trans s⟩

end Representation.SuzukiSmallDegree
