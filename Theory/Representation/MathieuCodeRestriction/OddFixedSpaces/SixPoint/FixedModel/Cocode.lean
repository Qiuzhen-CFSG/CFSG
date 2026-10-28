module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Coordinates
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Representation.MathieuCodeRestriction.Duality

/-!
# The six-point fixed cocode model

For a subgroup of order three with six common fixed points, extension by zero
identifies the binary six-point core with the actual fixed subspace of the
Mathieu cocode.  The proof uses the native Golay minimum distance, and hence
does not identify the cocode with an unrelated permutation model.  The same
map is then made equivariant for the normalizer.

Source: Aschbacher--Smith, H.15.7(2), printed pp.401--402.
-/

@[expose] public section

open Sporadic.Mathieu
open Representation.BinaryOffender
open scoped BigOperators Pointwise
namespace MathieuCode.SixPoint
noncomputable section
open scoped Classical

private theorem hammingNorm_extendWord_le (D : Subgroup M24)
    (v : FixedPoint D → ZMod 2) :
    hammingNorm (extendWord D v) ≤ Fintype.card (FixedPoint D) := by
  rw [Fintype.card_subtype]
  apply Finset.card_le_card
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  by_contra hn
  apply hi'
  have hn' : i ∉ FixedPoint D := by simpa using hn
  change (if h : i ∈ FixedPoint D then v ⟨i, h⟩ else 0) = 0
  rw [dif_neg hn']

theorem toFixedCocode_injective (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6) :
    Function.Injective (toFixedCocode D) := by
  intro v w hvw
  apply Subtype.ext
  have hz : extendCore D (v - w) ∈ codeInCore := by
    apply (Submodule.Quotient.mk_eq_zero codeInCore).mp
    change toCocode D (v - w) = 0
    rw [map_sub, show toCocode D v = toCocode D w from congrArg Subtype.val hvw, sub_self]
  have hg : (extendCore D (v - w)).val ∈ golay := hz
  have hzero : (extendCore D (v - w)).val = 0 := by
    by_contra hn
    have hmin := native_golay_minimum hg hn
    have hle := hammingNorm_extendWord_le D (v - w).val
    have hc : Fintype.card (FixedPoint D) = 6 := by
      simpa only [Nat.card_eq_fintype_card] using hD
    change 8 ≤ hammingNorm (extendWord D (v - w).val) at hmin
    rw [hc] at hle
    omega
  have hfun : extendWord D (v - w).val = 0 := hzero
  funext i
  have hi := congrFun hfun i.val
  exact sub_eq_zero.mp (by simpa only [extendWord_apply, Submodule.coe_sub, Pi.sub_apply, Pi.zero_apply] using hi)

theorem toFixedCocode_bijective (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6)
    (hdim : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation D) = 5) :
    Function.Bijective (toFixedCocode D) := by
  refine ⟨toFixedCocode_injective D hD, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (toFixedCocode_injective D hD)
  rw [finrank_fixedPoint_core D hD, hdim]

theorem extendCore_normalizer (D : Subgroup M24)
    (n : Subgroup.normalizer (D : Set M24))
    (v : BinaryPermutation.core (FixedPoint D)) :
    extendCore D (fixedPointCoreRepresentation D n v) =
      coreRepresentation n.val (extendCore D v) := by
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ MulAction.fixedPoints D (Fin 24)
  · have hni : n.val.val.symm i ∈ MulAction.fixedPoints D (Fin 24) :=
      normalizer_preserves_fixedPoints D n⁻¹ ⟨i, hi⟩
    change (if h : i ∈ MulAction.fixedPoints D (Fin 24) then
      v.val ((normalizerPerm D n).symm ⟨i, h⟩) else 0) =
      (if h : n.val.val.symm i ∈ MulAction.fixedPoints D (Fin 24) then
        v.val ⟨n.val.val.symm i, h⟩ else 0)
    rw [dif_pos hi, dif_pos hni]
    rfl
  · have hni : n.val.val.symm i ∉ MulAction.fixedPoints D (Fin 24) := by
      intro h
      have hh := normalizer_preserves_fixedPoints D n ⟨n.val.val.symm i, h⟩
      apply hi
      change n.val.val (n.val.val.symm i) ∈ MulAction.fixedPoints D (Fin 24) at hh
      simpa only [Equiv.apply_symm_apply] using hh
    change (if h : i ∈ MulAction.fixedPoints D (Fin 24) then _ else 0) =
      (if h : n.val.val.symm i ∈ MulAction.fixedPoints D (Fin 24) then _ else 0)
    rw [dif_neg hi, dif_neg hni]

theorem toCocode_normalizer (D : Subgroup M24)
    (n : Subgroup.normalizer (D : Set M24))
    (v : BinaryPermutation.core (FixedPoint D)) :
    toCocode D (fixedPointCoreRepresentation D n v) =
      cocodeRepresentation n.val (toCocode D v) := by
  change codeInCore.mkQ (extendCore D (fixedPointCoreRepresentation D n v)) = _
  rw [extendCore_normalizer]
  rfl

theorem toFixedCocode_normalizer (D : Subgroup M24)
    (n : Subgroup.normalizer (D : Set M24))
    (v : BinaryPermutation.core (FixedPoint D)) :
    toFixedCocode D (fixedPointCoreRepresentation D n v) =
      fixedCocodeRepresentation D n (toFixedCocode D v) := by
  apply Subtype.ext
  exact toCocode_normalizer D n v

def fixedPointCoreEquiv (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6)
    (hdim : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation D) = 5) :
    BinaryPermutation.core (FixedPoint D) ≃ₗ[ZMod 2]
      fixedSpace cocodeRepresentation D :=
  LinearEquiv.ofBijective (toFixedCocode D) (toFixedCocode_bijective D hD hdim)

def fixedPointCoreRepresentationEquiv (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6)
    (hdim : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation D) = 5) :
    (fixedPointCoreRepresentation D).Equiv (fixedCocodeRepresentation D) :=
  Representation.Equiv.mk (fixedPointCoreEquiv D hD hdim) (by
    intro n
    apply LinearMap.ext
    intro v
    exact toFixedCocode_normalizer D n v)

@[simp] theorem fixedPointCoreRepresentationEquiv_apply
    (D : Subgroup M24) (hD : Nat.card (FixedPoint D) = 6)
    (hdim : Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation D) = 5)
    (v : BinaryPermutation.core (FixedPoint D)) :
    fixedPointCoreRepresentationEquiv D hD hdim v = toFixedCocode D v := rfl

private theorem pair_fixed_points_of_order_three
    (D : Subgroup M24) (hD : Nat.card D = 3)
    {B : Finset (Fin 24)} (hB : B.card = 2)
    (hfix : ∀ d : D, (d.val • B) = B) :
    ∀ ⦃x : Fin 24⦄, x ∈ B → x ∈ MulAction.fixedPoints D (Fin 24) := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hB
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  have hpow (d : D) : d.val ^ 3 = (1 : M24) := by
    have hd : d ^ 3 = 1 := by simpa only [hD] using (pow_card_eq_one' (x := d))
    exact congrArg Subtype.val hd
  have hfixx (d : D) : d.val • x = x := by
    have hmem : d.val • x ∈ ({x, y} : Finset (Fin 24)) := by
      rw [← hfix d]
      exact Finset.smul_mem_smul_finset (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hxx | hxy'
    · exact hxx
    · have hmemy : d.val • y ∈ ({x, y} : Finset (Fin 24)) := by
        rw [← hfix d]
        exact Finset.smul_mem_smul_finset (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemy
      rcases hmemy with hyx | hyy
      · have hp := congrArg (fun g : M24 => g • x) (hpow d)
        have hp' : d.val • (d.val • (d.val • x)) = x := by
          simpa only [pow_succ, pow_zero, mul_smul, one_smul] using hp
        rw [hxy', hyx, hxy'] at hp'
        exact False.elim (hxy hp'.symm)
      · exact False.elim (hxy (d.val.val.injective (hxy'.trans hyy.symm)))
  have hfixy (d : D) : d.val • y = y := by
    have hmem : d.val • y ∈ ({x, y} : Finset (Fin 24)) := by
      rw [← hfix d]
      exact Finset.smul_mem_smul_finset (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hyx | hyy
    · exact False.elim (hxy (d.val.val.injective ((hfixx d).trans hyx.symm)))
    · exact hyy
  rcases hz with rfl | rfl
  · intro d
    exact hfixx d
  · intro d
    exact hfixy d

theorem cocodeO2_fixed_pair_iff (D : Subgroup M24)
    (hD : Nat.card D = 3) :
    cocodeO2 ∩ (fixedSpace cocodeRepresentation D : Set Cocode) =
      {v | ∃ i j : FixedPoint D, i ≠ j ∧ v = toCocode D (pair i j)} := by
  ext v
  constructor
  · rintro ⟨⟨B, hB, rfl⟩, hv⟩
    have hfix : ∀ d : D, d.val • B = B := fun d =>
      (pairVector_fixed_iff d.val ⟨B, hB⟩).mp (hv d)
    have hsub := pair_fixed_points_of_order_three D hD hB hfix
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hB
    let i : FixedPoint D := ⟨x, hsub (by simp)⟩
    let j : FixedPoint D := ⟨y, hsub (by simp)⟩
    refine ⟨i, j, ?_, ?_⟩
    · simpa [i, j] using hxy
    · exact (toCocode_pair D i j (by simpa [i, j] using hxy)).symm
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨toCocode_pair_mem D i j hij, ?_⟩
    exact toCocode_mem_fixedSpace D (pair i j)

theorem m23CocodeO2_fixed_pair_iff (D : Subgroup M24)
    (hD : Nat.card D = 3) (h0 : (0 : Fin 24) ∈ MulAction.fixedPoints D (Fin 24)) :
    m23CocodeO2 ∩ (fixedSpace cocodeRepresentation D : Set Cocode) =
      {v | ∃ i j : FixedPoint D, i ≠ j ∧ i.val = 0 ∧ v = toCocode D (pair i j)} := by
  ext v
  constructor
  · rintro ⟨⟨B, hB, h0B, rfl⟩, hv⟩
    have hfix : ∀ d : D, d.val • B = B := fun d =>
      (pairVector_fixed_iff d.val ⟨B, hB⟩).mp (hv d)
    have hsub := pair_fixed_points_of_order_three D hD hB hfix
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hB
    have hx0 : x = 0 ∨ y = 0 := by simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using h0B
    rcases hx0 with rfl | rfl
    · let i : FixedPoint D := ⟨0, h0⟩
      let j : FixedPoint D := ⟨y, hsub (by simp)⟩
      refine ⟨i, j, ?_, rfl, ?_⟩
      · simpa [i, j] using hxy
      · exact (toCocode_pair D i j (by simpa [i, j] using hxy)).symm
    · let i : FixedPoint D := ⟨0, h0⟩
      let j : FixedPoint D := ⟨x, hsub (by simp)⟩
      refine ⟨i, j, ?_, rfl, ?_⟩
      · simpa [i, j] using hxy.symm
      · rw [toCocode_pair D i j (by simpa [i, j] using hxy.symm)]
        simp only [i, j, Finset.pair_comm]
  · rintro ⟨i, j, hij, hi0, rfl⟩
    refine ⟨toCocode_pointPair_mem D i j hi0 hij, ?_⟩
    exact toCocode_mem_fixedSpace D (pair i j)

end
end MathieuCode.SixPoint
