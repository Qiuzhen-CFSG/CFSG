module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Commutator

universe u

open scoped commutatorElement

/-!
Conjugation and quotient consequences for the relative-root series.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_pow_conj_mem_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i n : ℕ) (hi : 0 < i)
    {x z : Variety.Point K}
    (hx : x ∈ RelativeRootSeries D e base.support coeff J i)
    (hz : z ∈ RelativeRootSeries D e base.support coeff J (i + 1)) :
    x ^ n * z * (x ^ n)⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
  have hnorm : x ∈ Subgroup.normalizer
      (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K)) :=
    relativeRootSeries_le_normalizer D C P e base coeff hCoeff hC J i hi hx
  have hpow : x ^ n ∈ Subgroup.normalizer
      (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K)) :=
    (Subgroup.normalizer
      (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K))).pow_mem hnorm n
  exact (Subgroup.mem_normalizer_iff.mp hpow z).1 hz

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_zpow_conj_mem_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    {x z : Variety.Point K}
    (hx : x ∈ RelativeRootSeries D e base.support coeff J i)
    (hz : z ∈ RelativeRootSeries D e base.support coeff J (i + 1))
    (n : ℤ) :
    x ^ n * z * (x ^ n)⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
  have hnorm : x ∈ Subgroup.normalizer
      (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K)) :=
    relativeRootSeries_le_normalizer D C P e base coeff hCoeff hC J i hi hx
  have hzpow : x ^ n ∈ Subgroup.normalizer
      (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K)) :=
    (Subgroup.normalizer
      (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K))).zpow_mem hnorm n
  exact (Subgroup.mem_normalizer_iff.mp hzpow z).1 hz

end

open scoped commutatorElement

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_quotient_commutative_of_next_layer_normal
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    (hN : ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
      (RelativeRootSeries D e base.support coeff J i)).Normal) :
    IsMulCommutative
      ((RelativeRootSeries D e base.support coeff J i) ⧸
        (RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
          (RelativeRootSeries D e base.support coeff J i)) := by
  let : ((RelativeRootSeries D e base.support coeff J (i + 1)).subgroupOf
      (RelativeRootSeries D e base.support coeff J i)).Normal := hN
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 <|
    by
      have hcomm :
          ⁅RelativeRootSeries D e base.support coeff J i,
            RelativeRootSeries D e base.support coeff J i⁆ ≤
              RelativeRootSeries D e base.support coeff J (i + 1) :=
        relativeRootSeries_commutator_same_layer_le_next_layer (D := D) (C := C) (P := P)
          (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
          (J := J) (i := i) hi
      have hmap :
          (_root_.commutator ↥(RelativeRootSeries D e base.support coeff J i)).map
            (RelativeRootSeries D e base.support coeff J i).subtype ≤
              RelativeRootSeries D e base.support coeff J (i + 1) := by
        rw [Subgroup.map_subtype_commutator]
        exact hcomm
      simpa [Subgroup.comap_subtype] using
        (Subgroup.map_le_iff_le_comap.mp hmap)

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_list_prod_conj_mem_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    {l : List (Variety.Point K)}
    (hl : ∀ x ∈ l, x ∈ RelativeRootSeries D e base.support coeff J i)
    {z : Variety.Point K}
    (hz : z ∈ RelativeRootSeries D e base.support coeff J (i + 1)) :
    l.prod * z * l.prod⁻¹ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
  induction l with
  | nil =>
      simpa
  | cons x xs ih =>
      have hx : x ∈ RelativeRootSeries D e base.support coeff J i := by
        exact hl x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ RelativeRootSeries D e base.support coeff J i := by
        intro y hy
        exact hl y (by simp [hy])
      have hxsProd : xs.prod ∈ RelativeRootSeries D e base.support coeff J i := by
        exact Subgroup.list_prod_mem _ hxs
      have hconj :
          (x * xs.prod) * z * (x * xs.prod)⁻¹ ∈
            RelativeRootSeries D e base.support coeff J (i + 1) :=
        relativeRootSeries_mul_conj_mem_next_layer (D := D) (C := C) (P := P)
          (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
          (J := J) (i := i) hi hx hxsProd hz
      simpa [List.prod_cons, mul_assoc] using hconj

end

open scoped commutatorElement

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_zpow_commutator_mem_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    {x z : Variety.Point K}
    (hx : x ∈ RelativeRootSeries D e base.support coeff J i)
    (hz : z ∈ RelativeRootSeries D e base.support coeff J (i + 1))
    (n : ℤ) :
    ⁅x ^ n, z⁆ ∈ RelativeRootSeries D e base.support coeff J (i + 1) := by
  classical
  let Snext : Subgroup (Variety.Point K) := RelativeRootSeries D e base.support coeff J (i + 1)
  have hconj :
      x ^ n * z * (x ^ n)⁻¹ ∈ Snext := by
    exact relativeRootSeries_zpow_conj_mem_next_layer (D := D) (C := C) (P := P)
      (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
      (J := J) (i := i) hi hx hz n
  have hzInv : z⁻¹ ∈ Snext := Snext.inv_mem hz
  simpa [commutatorElement_def, mul_assoc] using Snext.mul_mem hconj hzInv

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_list_prod_normalizer_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i)
    {l : List (Variety.Point K)}
    (hl : ∀ x ∈ l, x ∈ RelativeRootSeries D e base.support coeff J i) :
    l.prod ∈ Subgroup.normalizer (RelativeRootSeries D e base.support coeff J (i + 1) :
      Set (Variety.Point K)) := by
  have hprod : l.prod ∈ RelativeRootSeries D e base.support coeff J i := by
    exact Subgroup.list_prod_mem _ hl
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact relativeRootSeries_list_prod_conj_mem_next_layer (D := D) (C := C) (P := P)
      (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
      (J := J) (i := i) hi hl hz
  · intro hz
    have hprodInv : l.prod⁻¹ ∈ RelativeRootSeries D e base.support coeff J i := by
      simpa using (RelativeRootSeries D e base.support coeff J i).inv_mem hprod
    have hinvNorm : l.prod⁻¹ ∈ Subgroup.normalizer
        (RelativeRootSeries D e base.support coeff J (i + 1) : Set (Variety.Point K)) :=
      relativeRootSeries_le_normalizer (D := D) (C := C) (P := P) (e := e)
        (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC) (J := J)
        (i := i) hi hprodInv
    have hconj :
        l.prod⁻¹ * (l.prod * z * l.prod⁻¹) * l.prod⁻¹⁻¹ ∈
          RelativeRootSeries D e base.support coeff J (i + 1) := by
      exact (Subgroup.mem_normalizer_iff.mp hinvNorm (l.prod * z * l.prod⁻¹)).1 hz
    have hEq : l.prod⁻¹ * (l.prod * z * l.prod⁻¹) * l.prod = z := by
      group
    simpa [hEq] using hconj

end

open scoped commutatorElement

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_zpow_commutator_generated_le_next_layer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (hC : IsChevalleySystem D C P e base)
    (J : Set D.Root) (i : ℕ) (hi : 0 < i) :
    Subgroup.closure
      {y : Variety.Point K |
        ∃ x : Variety.Point K,
          x ∈ RelativeRootSeries D e base.support coeff J i ∧
        ∃ z : Variety.Point K,
          z ∈ RelativeRootSeries D e base.support coeff J (i + 1) ∧
        ∃ n : ℤ, y = ⁅x ^ n, z⁆} ≤
      RelativeRootSeries D e base.support coeff J (i + 1) := by
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with ⟨x, hx, z, hz, n, rfl⟩
  exact relativeRootSeries_zpow_commutator_mem_next_layer (D := D) (C := C) (P := P)
    (e := e) (base := base) (coeff := coeff) (hCoeff := hCoeff) (hC := hC)
    (J := J) (i := i) hi hx hz n

end
end Theory.AlgebraicGroup
