module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_k1_one_mem
public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_k1_mul_mem
public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_k1_inv_mem

/-!
This internal module proves normality of `K^σ Z` inside `K₁` in GLS3,
Theorem 2.1.8.  Write the twisted defect of `x ∈ K₁` as
`d(x) = x⁻¹ σ(x) ∈ Z`.  Centrality of `Z` shows that
`σ(x a x⁻¹) = x a x⁻¹` for every fixed point `a`, while conjugation preserves
the central factor `Z`.  Decomposing an element of `K^σ ⊔ Z` into these two
factors therefore proves the required subgroup normality.  The local subgroup
definitions remain verbatim copies of the dependent construction used by the
main theorem.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_8_n_normal
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (Z : ClosedSubgroup K)
    (hZ : Z.toSubgroup ≤ Subgroup.center (Variety.Point K)) :
    let G := Variety.Point K
    let Kfix : Subgroup G :=
      { carrier := {g | σ.onPoints g = g}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          change σ.onPoints (a * b) = a * b
          rw [map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          change σ.onPoints a⁻¹ = a⁻¹
          rw [map_inv, ha] }
    let K₁ : Subgroup G :=
      { carrier := {g | g⁻¹ * σ.onPoints g ∈ Z.toSubgroup}
        one_mem' := theorem_2_1_8_k1_one_mem σ Z
        mul_mem' := by
          intro a b ha hb
          exact theorem_2_1_8_k1_mul_mem σ Z hZ ha hb
        inv_mem' := by
          intro a ha
          exact theorem_2_1_8_k1_inv_mem σ Z hZ ha }
    let N := Kfix ⊔ Z.toSubgroup
    (N.subgroupOf K₁).Normal := by
  dsimp only
  let Kfix : Subgroup (Variety.Point K) :=
    { carrier := {g | σ.onPoints g = g}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change σ.onPoints (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change σ.onPoints a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let K₁ : Subgroup (Variety.Point K) :=
    { carrier := {g | g⁻¹ * σ.onPoints g ∈ Z.toSubgroup}
      one_mem' := theorem_2_1_8_k1_one_mem σ Z
      mul_mem' := theorem_2_1_8_k1_mul_mem σ Z hZ
      inv_mem' := theorem_2_1_8_k1_inv_mem σ Z hZ }
  have hZnormal : Z.toSubgroup.Normal := by
    constructor
    intro z hz g
    have hcomm := Subgroup.mem_center_iff.mp (hZ hz) g
    rw [hcomm]
    simpa using hz
  let _ : Z.toSubgroup.Normal := hZnormal
  constructor
  intro n hn x
  change (x : Variety.Point K) * n * (x : Variety.Point K)⁻¹ ∈ Kfix ⊔ Z.toSubgroup
  obtain ⟨a, ha, z, hz, hnaz⟩ := Subgroup.mem_sup_of_normal_right.mp hn
  have hnaz' : a * z = (n : Variety.Point K) := hnaz
  rw [← hnaz']
  have hx : (x : Variety.Point K)⁻¹ * σ.onPoints x ∈ Z.toSubgroup := x.property
  have hfixed : (x : Variety.Point K) * a * (x : Variety.Point K)⁻¹ ∈ Kfix := by
    change σ.onPoints ((x : Variety.Point K) * a * (x : Variety.Point K)⁻¹) =
      (x : Variety.Point K) * a * (x : Variety.Point K)⁻¹
    have hdcomm : ((x : Variety.Point K)⁻¹ * σ.onPoints x) * a =
        a * ((x : Variety.Point K)⁻¹ * σ.onPoints x) :=
      (Subgroup.mem_center_iff.mp (hZ hx) a).symm
    rw [map_mul, map_mul, ha, map_inv]
    calc
      σ.onPoints x * a * (σ.onPoints x)⁻¹ =
          (x : Variety.Point K) * (((x : Variety.Point K)⁻¹ * σ.onPoints x) * a) *
            (σ.onPoints x)⁻¹ := by simp [mul_assoc]
      _ = (x : Variety.Point K) * (a * ((x : Variety.Point K)⁻¹ * σ.onPoints x)) *
            (σ.onPoints x)⁻¹ := by rw [hdcomm]
      _ = (x : Variety.Point K) * a * (x : Variety.Point K)⁻¹ := by simp [mul_assoc]
  have hzconj : (x : Variety.Point K) * z * (x : Variety.Point K)⁻¹ ∈ Z.toSubgroup :=
    hZnormal.conj_mem z hz x
  have hfactor : (x : Variety.Point K) * (a * z) * (x : Variety.Point K)⁻¹ =
      ((x : Variety.Point K) * a * (x : Variety.Point K)⁻¹) *
        ((x : Variety.Point K) * z * (x : Variety.Point K)⁻¹) := by
    simp [mul_assoc]
  rw [hfactor]
  exact (Kfix ⊔ Z.toSubgroup).mul_mem
    (Subgroup.mem_sup_left hfixed) (Subgroup.mem_sup_right hzconj)

end Theory.AlgebraicGroup
