module

public import Stellmacher.PushingUp.SL2TwoNaturalSylow
public import Theory.GroupAction.Quotient

/-!
# An involution in a natural quotient forces exponent two

Let Z ≤ U be central in U and have exponent dividing two. Suppose that an
ambient subgroup L induces, through a surjective actor map, the natural
SL₂(2) action on the literal quotient U/(Z.subgroupOf U). If U contains an
involution outside Z, then U is elementary abelian. Neither U nor the ambient
group is assumed finite. The normality witness only forms this literal
quotient, and the given quotient-action instance is retained throughout.

The natural module is transitive on its three nonzero vectors. Therefore every
nontrivial Z-coset has a representative conjugate to the given involution.
Multiplying that representative by a central element of exponent two still
has square one. Thus every element of U has square one, which also forces
commutativity. The matrix transitivity calculation is kernel checked.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.3)(f), journal
p. 15, the final p = 2 contradiction used in the proof of Theorem 2 of the
N-group paper, `refs/latex/stellmacher-n-group.tex`. This module establishes
only the natural-quotient implication; the graph application must identify
its literal quotient with the source's central quotient.
-/

namespace Stellmacher.PushingUp

universe u v

private theorem elementaryAbelian_of_central_involution_coset_transitive
    {G : Type u} [Group G] (U Z F : Subgroup G)
    (hZU : Z ≤ U)
    (hZcentral : ∀ z : G, z ∈ Z → ∀ u : G, u ∈ U → z * u = u * z)
    (hZsq : ∀ z : G, z ∈ Z → z ^ 2 = 1)
    (x : G) (_hxU : x ∈ U) (_hxZ : x ∉ Z) (hxsq : x ^ 2 = 1)
    (horbit : ∀ u : G, u ∈ U → u ∉ Z →
      ∃ f : G, f ∈ F ∧ ∃ z : G, z ∈ Z ∧ u = (f * x * f⁻¹) * z) :
    IsElementaryAbelian 2 U := by
  have hpow : ∀ u : G, u ∈ U → u ^ 2 = 1 := by
    intro u hu
    by_cases huz : u ∈ Z
    · exact hZsq u huz
    obtain ⟨f, hfF, z, hzZ, rfl⟩ := horbit u hu huz
    have hzU : z ∈ U := hZU hzZ
    have hconjU : f * x * f⁻¹ ∈ U := by
      have hcancel : ((f * x * f⁻¹) * z) * z⁻¹ ∈ U :=
        U.mul_mem hu (U.inv_mem hzU)
      simpa [mul_assoc] using hcancel
    have hconjsq : (f * x * f⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hxsq]
      simp
    have hcomm : Commute (f * x * f⁻¹) z :=
      (hZcentral z hzZ _ hconjU).symm
    rw [hcomm.mul_pow, hconjsq, hZsq z hzZ]
    simp
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (show (a : G) * (b : G) =
          (b : G) * (a : G) from ?_)⟩⟩
      exponent_dvd_p := ?_ }
  · have hab : ((a : G) * (b : G)) ^ 2 = 1 :=
      hpow ((a : G) * (b : G)) (U.mul_mem a.property b.property)
    have ha : (a : G)⁻¹ = a :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hpow a a.property)
    have hb : (b : G)⁻¹ = b :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hpow b b.property)
    have habInv : ((a : G) * (b : G))⁻¹ = (a : G) * (b : G) :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hab)
    calc
      (a : G) * (b : G) = ((a : G) * (b : G))⁻¹ := habInv.symm
      _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
      _ = (b : G) * (a : G) := by rw [ha, hb]
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply Subtype.ext
    exact hpow a a.property


private theorem sl2Two_mulVec_transitive_nonzero
    (x y : Fin 2 → ZMod 2) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      Matrix.mulVec A.1 x = y := by
  decide +revert +kernel

private theorem naturalSL2Two_transitive_nonidentity
    {A : Type u} {W : Type v} [Group A] [Group W]
    [MulDistribMulAction A W]
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat : IsNaturalSL2TwoActionAlong W eA)
    (x y : W) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : A, a • x = y := by
  obtain ⟨eW, heW⟩ := hNat
  have hxcoord : eW (Additive.ofMul x) ≠ 0 := by simpa using hx
  have hycoord : eW (Additive.ofMul y) ≠ 0 := by simpa using hy
  obtain ⟨mat, hmat⟩ := sl2Two_mulVec_transitive_nonzero
    (eW (Additive.ofMul x)) (eW (Additive.ofMul y)) hxcoord hycoord
  let a : A := eA.symm mat
  refine ⟨a, ?_⟩
  apply Additive.ofMul.injective
  apply eW.injective
  calc
    eW (Additive.ofMul (a • x)) =
        Matrix.mulVec (eA a).1 (eW (Additive.ofMul x)) := heW a x
    _ = eW (Additive.ofMul y) := by simpa [a] using hmat

/-- A natural `SL₂(2)` action on the literal quotient `U/Z`, realized by
ambient conjugation of a surjective actor, is transitive on the nontrivial
ambient `Z`-cosets. -/
private theorem naturalSL2Two_coset_orbit_of_surjective_conjugation
    {H : Type u} {A : Type v} [Group H] [Group A]
    (L U Z : Subgroup H)
    (hZnormal : (Z.subgroupOf U).Normal)
    [MulDistribMulAction A (U ⧸ Z.subgroupOf U)]
    (f : L →* A) (hf : Function.Surjective f)
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat : IsNaturalSL2TwoActionAlong (U ⧸ Z.subgroupOf U) eA)
    (hconjU : ∀ l : L, ∀ w : U,
      (l : H) * (w : H) * (l : H)⁻¹ ∈ U)
    (hact : ∀ (l : L) (w : U),
      (f l) • (QuotientGroup.mk' (Z.subgroupOf U)) w =
        (QuotientGroup.mk' (Z.subgroupOf U))
          ⟨(l : H) * (w : H) * (l : H)⁻¹, hconjU l w⟩) :
    ∀ x : U, (QuotientGroup.mk' (Z.subgroupOf U)) x ≠ 1 →
      ∀ w : U, (QuotientGroup.mk' (Z.subgroupOf U)) w ≠ 1 →
        ∃ l : L, ∃ z : Z,
          (w : H) = (l : H) * (x : H) * (l : H)⁻¹ * (z : H) := by
  intro x hx w hw
  obtain ⟨a, ha⟩ := naturalSL2Two_transitive_nonidentity eA hNat
    ((QuotientGroup.mk' (Z.subgroupOf U)) x)
    ((QuotientGroup.mk' (Z.subgroupOf U)) w) hx hw
  obtain ⟨l, hl⟩ := hf a
  have hquot :
      (QuotientGroup.mk' (Z.subgroupOf U))
          ⟨(l : H) * (x : H) * (l : H)⁻¹, hconjU l x⟩ =
        (QuotientGroup.mk' (Z.subgroupOf U)) w := by
    calc
      (QuotientGroup.mk' (Z.subgroupOf U))
          ⟨(l : H) * (x : H) * (l : H)⁻¹, hconjU l x⟩ =
          (f l) • (QuotientGroup.mk' (Z.subgroupOf U)) x := (hact l x).symm
      _ = a • (QuotientGroup.mk' (Z.subgroupOf U)) x := by rw [hl]
      _ = (QuotientGroup.mk' (Z.subgroupOf U)) w := ha
  obtain ⟨z, hz, hzw⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := Z.subgroupOf U)).mp hquot
  refine ⟨l, ⟨(z : H), Subgroup.mem_subgroupOf.mp hz⟩, ?_⟩
  simpa using congrArg Subtype.val hzw.symm


/-- An outside involution and a natural SL₂(2) action on the quotient by a
central exponent-two subgroup make the whole subgroup elementary abelian. -/
public theorem elementaryAbelian_of_natural_quotient_involution
    {H : Type u} {A : Type v} [Group H] [Group A]
    (L U Z : Subgroup H) (hZU : Z ≤ U)
    (hZcentral : ∀ z : H, z ∈ Z → ∀ u : H, u ∈ U → z * u = u * z)
    (hZsq : ∀ z : H, z ∈ Z → z ^ 2 = 1)
    (hZnormal : (Z.subgroupOf U).Normal)
    [MulDistribMulAction A (U ⧸ Z.subgroupOf U)]
    (f : L →* A) (hf : Function.Surjective f)
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat : IsNaturalSL2TwoActionAlong (U ⧸ Z.subgroupOf U) eA)
    (hconjU : ∀ l : L, ∀ w : U,
      (l : H) * (w : H) * (l : H)⁻¹ ∈ U)
    (hact : ∀ (l : L) (w : U),
      (f l) • (QuotientGroup.mk' (Z.subgroupOf U)) w =
        (QuotientGroup.mk' (Z.subgroupOf U))
          ⟨(l : H) * (w : H) * (l : H)⁻¹, hconjU l w⟩)
    (x : H) (hxU : x ∈ U) (hxZ : x ∉ Z) (hxsq : x ^ 2 = 1) :
    IsElementaryAbelian 2 U := by
  apply elementaryAbelian_of_central_involution_coset_transitive
    U Z L hZU hZcentral hZsq x hxU hxZ hxsq
  intro w hwU hwZ
  have hxq : (QuotientGroup.mk' (Z.subgroupOf U)) ⟨x, hxU⟩ ≠ 1 := by
    intro h
    exact hxZ ((QuotientGroup.eq_one_iff (N := Z.subgroupOf U) _).mp h)
  have hwq : (QuotientGroup.mk' (Z.subgroupOf U)) ⟨w, hwU⟩ ≠ 1 := by
    intro h
    exact hwZ ((QuotientGroup.eq_one_iff (N := Z.subgroupOf U) _).mp h)
  obtain ⟨l, z, hz⟩ := naturalSL2Two_coset_orbit_of_surjective_conjugation
    L U Z hZnormal f hf eA hNat hconjU hact ⟨x, hxU⟩ hxq ⟨w, hwU⟩ hwq
  exact ⟨l, l.property, z, z.property, hz⟩

end Stellmacher.PushingUp
