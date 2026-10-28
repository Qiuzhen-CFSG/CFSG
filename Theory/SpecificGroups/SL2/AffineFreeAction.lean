module

public import Theory.SpecificGroups.SL2.SL23IntoSL25
public import Theory.SpecificGroups.SL2.PrimePlaneAction
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Free coprime subgroups in determinant-one plane actions

A determinant-one matrix fixing a nonzero vector is unipotent, so its order
in prime characteristic p divides p. Thus a subgroup of order prime to p
acts freely off zero. For a faithful action of a perfect group on an
elementary abelian plane, the determinant is trivial and the same conclusion
holds on the original elementary group, through its canonical vector space.

In particular the actual embedding SL₂(3) → SL₂(5) supplies a free subgroup
of order 24 in every faithful SL₂(5) action on a p-plane with p > 3. The
kernel prime p need not equal five. This is the exceptional extension case
in the last sentence of Aschbacher–Smith, Lemma 8.2.7, printed p.718, with
extension alternatives from A.3.6 and A.3.12–13. The unipotent calculation
is adapted from `SL2/PrimeFieldOddSubgroups.lean`.
-/

public section
open Matrix Subgroup
open scoped IsMulCommutative
namespace Matrix.SpecialLinearGroup.AffineFreeAction

private theorem char_pow_eq_one_of_fixed_vector {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (A : SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 → F) (hv : v ≠ 0) (hfix : A.val *ᵥ v = v) : A ^ p = 1 := by
  have hd : det (A.val - 1) = 0 := exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by simpa only [sub_mulVec, one_mulVec, sub_eq_zero] using hfix⟩
  have ha := A.property
  have ht : A.val 0 0 + A.val 1 1 = 2 := by
    simp only [det_fin_two, sub_apply, one_apply, Fin.isValue, ite_true,
      zero_ne_one, one_ne_zero, ite_false, sub_zero] at hd
    simp only [det_fin_two] at ha
    linear_combination ha - hd
  simp only [det_fin_two] at ha
  have hn : (A.val - 1) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination A.val 0 0 * ht - ha
    · linear_combination A.val 0 1 * ht
    · linear_combination A.val 1 0 * ht
    · linear_combination A.val 1 1 * ht - ha
  let : CharP (Matrix (Fin 2) (Fin 2) F) p := {
    cast_eq_zero_iff k := by
      simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
        CharP.cast_eq_zero_iff F p k, forall_const]
  }
  have hnp : (A.val - 1) ^ p = 0 := pow_eq_zero_of_le (Fact.out : p.Prime).two_le hn
  apply Subtype.ext
  change A.val ^ p = 1
  calc
    A.val ^ p = ((A.val - 1) + 1) ^ p := by rw [sub_add_cancel]
    _ = (A.val - 1) ^ p + 1 ^ p := add_pow_char_of_commute p (Commute.one_right _)
    _ = 1 := by rw [hnp, one_pow, zero_add]

/-- A coprime-order determinant-one matrix cannot fix a nonzero vector unless it is one. -/
theorem eq_one_of_fixed_vector_of_coprime {F : Type*} [Field F]
    {p m : ℕ} [Fact p.Prime] [CharP F p]
    (A : SpecialLinearGroup (Fin 2) F) (hcop : p.Coprime m) (hm : A ^ m = 1)
    (v : Fin 2 → F) (hv : v ≠ 0) (hfix : A.val *ᵥ v = v) : A = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [← hcop.gcd_eq_one]
  exact Nat.dvd_gcd
    (orderOf_dvd_of_pow_eq_one (char_pow_eq_one_of_fixed_vector A v hv hfix))
    (orderOf_dvd_of_pow_eq_one hm)

/-- Coprime subgroups act freely in a faithful perfect-group action on an elementary plane. -/
theorem fixedPointFree_of_faithful_perfect_plane_action
    {Q N : Type*} [Group Q] [Group.IsPerfect Q] [Group N] [Finite N]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p N]
    (hN : Nat.card N = p ^ 2) (α : Q →* MulAut N) (hα : Function.Injective α)
    (C : Subgroup Q) (hcop : p.Coprime (Nat.card C)) :
    ∀ c : C, c ≠ 1 → MonoidHom.FixedPointFree (α c) := by
  classical
  have hpow : p ^ Module.finrank (ZMod p) (Additive N) = p ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive N)
    change Nat.card N = _ at hsize
    simpa only [Nat.card_zmod, hN] using hsize.symm
  have hdim : Module.finrank (ZMod p) (Additive N) = 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt hpow
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive N) hdim
  let : MulDistribMulAction Q N := MulDistribMulAction.compHom N α
  let ρ := Representation.ofElementaryAbelianAction (A := Q) (G := N) (p := p)
  have hρ : Function.Injective ρ := by
    intro x y h
    apply hα
    ext n
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod p) (Additive N) => f (Additive.ofMul n)) h)
  let f : Q →* Matrix (Fin 2) (Fin 2) (ZMod p) :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ
  have hf : Function.Injective f := (LinearMap.toMatrixAlgEquiv b).injective.comp hρ
  have hdet (g : Q) : (f g).det = 1 := by
    let d := (Matrix.detMonoidHom.comp f).toHomUnits
    have hd : d = 1 := by
      apply MonoidHom.ker_eq_top_iff.mp
      apply top_unique
      rw [← Group.IsPerfect.commutator_eq_top (G := Q)]
      exact Abelianization.commutator_subset_ker d
    exact congrArg Units.val (DFunLike.congr_fun hd g)
  let σ : Q →* SpecialLinearGroup (Fin 2) (ZMod p) := {
    toFun g := ⟨f g, hdet g⟩
    map_one' := Subtype.ext f.map_one
    map_mul' x y := Subtype.ext (f.map_mul x y) }
  have hσ : Function.Injective σ := fun _ _ h => hf (congrArg Subtype.val h)
  intro c hc n hn
  by_contra hn1
  have hv : (fun i => b.repr (Additive.ofMul n) i) ≠ 0 := by
    intro h
    apply hn1
    apply Additive.ofMul.injective
    apply b.repr.injective
    ext i
    simpa using congrFun h i
  have hfix : (σ c).val *ᵥ (fun i => b.repr (Additive.ofMul n) i) =
      (fun i => b.repr (Additive.ofMul n) i) := by
    change (LinearMap.toMatrix b b (ρ c)) *ᵥ (b.repr (Additive.ofMul n)) = _
    rw [LinearMap.toMatrix_mulVec_repr]
    change (fun i => b.repr (Additive.ofMul (α c n)) i) = _
    rw [hn]
  have hcm : σ c ^ Nat.card C = 1 := by
    have hcPow : (c : Q) ^ Nat.card C = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := c))
    rw [← map_pow, hcPow, map_one]
  have hc1 := eq_one_of_fixed_vector_of_coprime (σ c) hcop hcm _ hv hfix
  exact hc (Subtype.ext (hσ (hc1.trans σ.map_one.symm)))

/-- Every faithful SL₂(5) action on an elementary p-plane, p > 3, contains free actors of order 24. -/
theorem exists_free_twentyFour_sl25
    {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p N] (hp : 3 < p) (hN : Nat.card N = p ^ 2)
    (α : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* MulAut N)
    (hα : Function.Injective α) :
    ∃ C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)),
      Nat.card C = 24 ∧ ∀ c : C, c ≠ 1 → MonoidHom.FixedPointFree (α c) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := PrimePlaneAction.perfect (p := 5) (by decide)
  let f := GLS3.Chapter5.SchurPresentation.sl23IntoSL25
  let C := f.range
  have hc : Nat.card C = 24 := by
    calc
      Nat.card C = Nat.card GLS3.Chapter5.SchurPresentation.SL23 :=
        (Nat.card_congr (Equiv.ofInjective f
          GLS3.Chapter5.SchurPresentation.sl23IntoSL25_injective)).symm
      _ = 24 := by rw [Nat.card_eq_fintype_card]; decide
  have hcop : p.Coprime (Nat.card C) := by
    rw [hc, show 24 = 2 ^ 3 * 3 by decide]
    apply Nat.Coprime.mul_right
    · exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).pow_right 3
    · exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) hp)
  exact ⟨C, hc, fixedPointFree_of_faithful_perfect_plane_action hN α hα C hcop⟩

end Matrix.SpecialLinearGroup.AffineFreeAction
