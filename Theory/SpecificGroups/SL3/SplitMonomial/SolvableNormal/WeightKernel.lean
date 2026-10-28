module

public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.Representation.RankThreePGroupIrreducible

/-!
# Odd order of the weight-centralizer kernel in SL₃

Let Q be a nonabelian three-subgroup of SL₃ over a finite field of
characteristic different from three, and let A be an abelian subgroup of
index three in Q. Then C(A) ∩ N(Q) has odd order.

An involution in this intersection induces an automorphism α of Q fixing A
pointwise. Normality and self-centralization of A put x⁻¹α(x) in A. Since α
fixes this displacement and is involutive, the displacement squares to one,
so it is trivial in the three-group. Thus the involution centralizes Q.
The faithful natural action of Q is absolutely irreducible, so Schur's lemma
makes its ambient centralizer scalar. Determinant one then gives cube one,
which excludes a nonidentity involution. Cauchy's theorem gives odd order.

This is the weight-kernel calculation for the alternative normalizer bound
in the solvable case of GLS3, Theorem 6.5.3(a–d),
`refs/KGroup/GLS3/chapter6.tex`, used in Aschbacher–Smith, Proposition 1.3.4,
printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

open Subgroup Representation

namespace Matrix.SL3.SplitMonomial

private theorem involutive_aut_eq_of_fixes_selfCentralizing
    {G : Type*} [Group G] (hG : IsPGroup 3 G)
    (A : Subgroup G) [A.Normal] (hC : centralizer (A : Set G) = A)
    (α : MulAut G) (hfix : ∀ a ∈ A, α a = a) (hsq : ∀ x, α (α x) = x) :
    ∀ x, α x = x := by
  intro x
  let c := x⁻¹ * α x
  have hc : c ∈ A := by
    rw [← hC]
    intro a ha
    have hb : α x * a * (α x)⁻¹ = x * a * x⁻¹ := by
      simpa only [map_mul, map_inv, hfix a ha] using
        hfix (x * a * x⁻¹) ((inferInstance : A.Normal).conj_mem a ha x)
    change a * (x⁻¹ * α x) = x⁻¹ * α x * a
    calc
      a * (x⁻¹ * α x) = x⁻¹ * (x * a * x⁻¹) * α x := by group
      _ = x⁻¹ * (α x * a * (α x)⁻¹) * α x := by rw [hb]
      _ = x⁻¹ * α x * a := by group
  have hc2 : c ^ 2 = 1 := by
    calc
      c ^ 2 = α c * c := by rw [hfix c hc, pow_two]
      _ = 1 := by dsimp [c]; rw [map_mul, map_inv, hsq]; group
  have hc1 : c = 1 := (hG.powEquiv (by decide : Nat.Coprime 3 2)).injective
    (by simpa using hc2)
  exact (inv_mul_eq_one.mp hc1).symm

private theorem centralizes_group_of_centralizes_index_three
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (A : Subgroup Q) (ha : IsMulCommutative A) (hi : A.index = 3)
    (d : G) (hdC : d ∈ centralizer (A.map Q.subtype : Set G))
    (hdN : d ∈ normalizer (Q : Set G)) (hd2 : d ^ 2 = 1) :
    d ∈ centralizer (Q : Set G) := by
  let : A.Normal := normal_of_index_three_of_isPGroup hQ A hi
  let α := Q.normalizerMonoidHom ⟨d, hdN⟩
  have hfix (a : Q) (ha : a ∈ A) : α a = a := by
    apply Subtype.ext
    change d * (a : G) * d⁻¹ = a
    have hc : (a : G) * d = d * (a : G) := hdC _ (mem_map_of_mem Q.subtype ha)
    rw [← hc]
    simp [mul_assoc]
  have hα2 : α ^ 2 = 1 := by
    change Q.normalizerMonoidHom ⟨d, hdN⟩ ^ 2 = 1
    rw [← map_pow]
    have he : (⟨d, hdN⟩ : normalizer (Q : Set G)) ^ 2 = 1 := Subtype.ext hd2
    rw [he, map_one]
  have hsq (x : Q) : α (α x) = x := by
    change (α ^ 2) x = x
    rw [hα2]
    rfl
  have heq := involutive_aut_eq_of_fixes_selfCentralizing hQ A
    (centralizer_eq_of_abelian_index_three hQ hn A ha hi) α hfix hsq
  intro x hx
  have he : d * x * d⁻¹ = x := congrArg Subtype.val (heq ⟨x, hx⟩)
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem exists_scalar_of_mem_centralizer
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : 3 ≠ p) (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (d : SpecialLinearGroup (Fin 3) F) (hd : d ∈ centralizer (Q : Set _)) :
    ∃ a : F, (d : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) a := by
  let R := Q.map SpecialLinearGroup.toGL
  let e := Q.equivMapOfInjective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
  have hRn : ¬ IsMulCommutative R := by
    intro hc
    let : IsMulCommutative R := hc
    apply hn
    refine ⟨⟨fun x y => e.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm' (e x : R) (e y : R)
  let ρ := (generalLinearNatural (F := F) 3).comp R.subtype
  let : IsAbsolutelyIrreducible ρ :=
    generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup (by decide : Odd 3)
      hp R (hQ.map SpecialLinearGroup.toGL) hRn
  let : IsIrreducible ρ :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  let f : Representation.End ρ := {
    toLinearMap := generalLinearNatural 3 (SpecialLinearGroup.toGL d)
    isIntertwining' := by
      intro g
      change generalLinearNatural 3 (SpecialLinearGroup.toGL d) * generalLinearNatural 3 g.val =
        generalLinearNatural 3 g.val * generalLinearNatural 3 (SpecialLinearGroup.toGL d)
      rw [← map_mul, ← map_mul]
      apply congrArg (generalLinearNatural 3)
      obtain ⟨x, hx, he⟩ := g.property
      rw [← he, ← map_mul, ← map_mul, hd x hx] }
  obtain ⟨a, ha⟩ := (isAbsolutelyIrreducible_iff_surjective ρ).mp inferInstance f
  have hlin : generalLinearNatural 3 (SpecialLinearGroup.toGL d) = a • LinearMap.id :=
    (congrArg IntertwiningMap.toLinearMap ha).symm
  refine ⟨a, ?_⟩
  have hmatrix := congrArg LinearMap.toMatrix' hlin
  simpa [generalLinearNatural, Matrix.GeneralLinearGroup.coe_toLin,
    ← Matrix.toLin'_apply', Matrix.smul_one_eq_diagonal] using hmatrix

private theorem eq_one_of_mem_centralizer_of_sq_eq_one
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : 3 ≠ p) (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (d : SpecialLinearGroup (Fin 3) F) (hd : d ∈ centralizer (Q : Set _))
    (hd2 : d ^ 2 = 1) : d = 1 := by
  obtain ⟨a, ha⟩ := exists_scalar_of_mem_centralizer hp Q hQ hn d hd
  have ha3 : a ^ 3 = 1 := by
    simpa [ha, Matrix.scalar_apply, Matrix.det_diagonal] using d.det_coe
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    change (d ^ 3 : SpecialLinearGroup (Fin 3) F).val = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [SpecialLinearGroup.coe_pow, ha, ← map_pow, ha3, map_one]
  have he : d ^ 3 = d := by rw [pow_succ, hd2, one_mul]
  exact he.symm.trans hd3

/-- The pointwise centralizer of an abelian index-three subgroup, intersected
with the normalizer of a nonabelian three-subgroup of SL₃, has odd order in
cross characteristic. Normality of A is required only inside Q and follows
from its index. -/
public theorem odd_card_weightCentralizer_normalizer
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : 3 ≠ p) (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (A : Subgroup Q) (ha : IsMulCommutative A) (hi : A.index = 3) :
    Odd (Nat.card ↥(centralizer (A.map Q.subtype : Set (SpecialLinearGroup (Fin 3) F)) ⊓
      normalizer (Q : Set (SpecialLinearGroup (Fin 3) F)))) := by
  let K := centralizer (A.map Q.subtype : Set (SpecialLinearGroup (Fin 3) F)) ⊓
    normalizer (Q : Set (SpecialLinearGroup (Fin 3) F))
  change Odd (Nat.card K)
  by_contra hodd
  have heven : 2 ∣ Nat.card K := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 heven
  have hd2 : (d : SpecialLinearGroup (Fin 3) F) ^ 2 = 1 := by
    have h : d ^ 2 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
    exact congrArg Subtype.val h
  have hdc := centralizes_group_of_centralizes_index_three Q hQ hn A ha hi d d.property.1 d.property.2 hd2
  have he : (d : SpecialLinearGroup (Fin 3) F) = 1 := eq_one_of_mem_centralizer_of_sq_eq_one hp Q hQ hn d hdc hd2
  have hd1 : d = 1 := Subtype.ext he
  simp [hd1] at hd

end Matrix.SL3.SplitMonomial
