module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.Pairs

/-!
# The distinguished fiber as elementary-group displacements

Centralizer confinement puts both factors of the Thompson fiber at z in M.
Writing its distinguished factor in A, normalization of A shows that the
product has order dividing four. Product order two would put the actor in A,
contrary to its nondistinguished class. Thus the product square is z and is
exactly the displacement `a⁻¹ * (b * a * b⁻¹)`. Conversely this nonidentity
displacement forces product order four and the correct half-order power.

No centralizing hypothesis on the initially chosen z is imposed. This
correspondence is valid before the moving-case cardinality calculation.
Source: GLS4, Chapter 2, proof of Lemma 12.8(b), `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
namespace ResidualFiberDisplacement

omit [Finite G] in
private theorem mem_Z_of_isConj (h : IsProductDisconnected Z M)
    {a b : G} (ha : a ∈ Z) (hab : IsConj a b) : b ∈ Z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  exact hg ▸ h.invariant g a ha

omit [Finite G] in
private theorem involution_of_isConj {a b : G} (ha : PFAppendixIII.IsInvolution a)
    (hab : IsConj a b) : PFAppendixIII.IsInvolution b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  exact BenderSuzuki.IsInvolution.map_of_injective ha
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

omit [Finite G] in
private theorem square_eq_one
    (h : IsProductDisconnected Z M)
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    {a : G} (ha : a ∈ closure (Z ∩ (M : Set G))) : a ^ 2 = 1 := by
  by_cases he : a = 1
  · simp [he]
  · exact (h.involutions a (show a ∈ Z ∩ (M : Set G) from hZA.symm ▸ ⟨ha, he⟩).1).sq_eq_one

private theorem pair_square
    (h : IsProductDisconnected Z M)
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    {z u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hu : PFAppendixIII.IsInvolution u) (huZ : u ∉ Z)
    (p : Fiber z u z) :
    p.val.1 ∈ closure (Z ∩ (M : Set G)) ∧ p.val.2 ∈ M ∧
      p.val.1⁻¹ * (p.val.2 * p.val.1 * p.val.2⁻¹) = z := by
  let a := p.val.1
  let b := p.val.2
  have haZ : a ∈ Z := mem_Z_of_isConj h hz p.property.1
  have haI := h.involutions a haZ
  have hbI : PFAppendixIII.IsInvolution b := involution_of_isConj hu p.property.2.1
  have hnot : ¬ IsConj z u := fun he => huZ (mem_Z_of_isConj h hz he)
  have hmem := fiber_mem_centralizer
    (orderOf_eq_prime (h.involutions z hz).sq_eq_one (h.involutions z hz).ne_one)
    (orderOf_eq_prime hu.sq_eq_one hu.ne_one) hnot p
  have haM : a ∈ M := h.centralizer_le hz hzM hmem.1
  have hbM : b ∈ M := h.centralizer_le hz hzM hmem.2
  have haA : a ∈ closure (Z ∩ (M : Set G)) := subset_closure ⟨haZ, haM⟩
  have hbN : b ∈ normalizer (closure (Z ∩ (M : Set G)) : Set G) := by
    rwa [distinguishedClosure_normalizer h]
  have hbaA : b * a * b⁻¹ ∈ closure (Z ∩ (M : Set G)) :=
    (mem_normalizer_iff.mp hbN a).mp haA
  have hprodA : (a * b)^2 ∈ closure (Z ∩ (M : Set G)) := by
    have he : (a * b)^2 = a * (b * a * b⁻¹) := by
      rw [hbI.inv_eq_self, pow_two]; group
    rw [he]
    exact (Subgroup.closure _).mul_mem haA hbaA
  have hfour : (a * b)^4 = 1 := by
    calc
      (a * b)^4 = ((a * b)^2)^2 := by rw [← pow_mul]
      _ = 1 := square_eq_one h hZA hprodA
  have hle : orderOf (a * b) ≤ 4 := Nat.le_of_dvd (by decide : 0 < 4)
    (orderOf_dvd_of_pow_eq_one hfour)
  have hpos := orderOf_pos (a * b)
  have htwo : Even (orderOf (a * b)) := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    have he := isConj_of_involutions_odd_product a b haI.sq_eq_one hbI.sq_eq_one ho
    exact hnot (p.property.1.trans (he.trans p.property.2.1.symm))
  have hne2 : orderOf (a * b) ≠ 2 := by
    intro he
    have hab : a * b = z := by
      simpa only [halfOrder_def, he, Nat.reduceDiv, pow_one] using
        (show halfOrder a b = z from p.property.2.2)
    have hbA : b ∈ closure (Z ∩ (M : Set G)) := by
      have hh := (closure (Z ∩ (M : Set G))).mul_mem haA (subset_closure ⟨hz, hzM⟩)
      rw [← hab, ← mul_assoc, ← pow_two, haI.sq_eq_one, one_mul] at hh
      exact hh
    have hbZ : b ∈ Z := (show b ∈ Z ∩ (M : Set G) from
      hZA.symm ▸ ⟨hbA, hbI.ne_one⟩).1
    exact huZ (mem_Z_of_isConj h hbZ p.property.2.1.symm)
  have horder : orderOf (a * b) = 4 := by obtain ⟨k, hk⟩ := htwo; omega
  refine ⟨haA, hbM, ?_⟩
  have hh : (a * b)^2 = z := by
    simpa only [halfOrder_def, horder, Nat.reduceDiv] using
      (show halfOrder a b = z from p.property.2.2)
  change a⁻¹ * (b * a * b⁻¹) = z
  calc
    _ = (a * b)^2 := by rw [haI.inv_eq_self, hbI.inv_eq_self, pow_two]; group
    _ = z := hh

/-- The distinguished fiber is the literal displacement equation on A,
with the actor running through its ambient conjugacy class inside M. -/
public def fiber_equiv_displacement_pairs
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    {z u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hu : PFAppendixIII.IsInvolution u) (huZ : u ∉ Z) :
    Fiber z u z ≃ ResidualDistinguishedDisplacementPairs Z M z u where
  toFun p := by
    have hp := pair_square h hZA hz hzM hu huZ p
    exact ⟨(⟨p.val.1, hp.1⟩, ⟨p.val.2, hp.2.1⟩), p.property.2.1, hp.2.2⟩
  invFun p := by
    let a : G := p.val.1
    let b : G := p.val.2
    have hbI := involution_of_isConj hu p.property.1
    have ha2 : a^2 = 1 := square_eq_one h hZA p.val.1.property
    have hai : a⁻¹ = a := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using ha2)
    have hsq : (a * b)^2 = z := by
      have hh := p.property.2
      change a⁻¹ * (b * a * b⁻¹) = z at hh
      rw [hai, hbI.inv_eq_self] at hh
      simpa only [pow_two, mul_assoc] using hh
    have ha1 : a ≠ 1 := by
      intro he
      have hh := hsq
      rw [he, one_mul, hbI.sq_eq_one] at hh
      exact (h.involutions z hz).ne_one hh.symm
    have haZ : a ∈ Z := (show a ∈ Z ∩ (M : Set G) from
      hZA.symm ▸ ⟨p.val.1.property, ha1⟩).1
    have h4 : (a*b)^4 = 1 := by
      calc
        (a*b)^4 = ((a*b)^2)^2 := by rw [← pow_mul]
        _ = 1 := by rw [hsq, (h.involutions z hz).sq_eq_one]
    have hle : orderOf (a*b) ≤ 4 := Nat.le_of_dvd (by decide : 0 < 4)
      (orderOf_dvd_of_pow_eq_one h4)
    have hdiv : orderOf (a*b) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hpos := orderOf_pos (a*b)
    have hn : ¬ orderOf (a*b) ∣ 2 := by
      intro hd
      exact (h.involutions z hz).ne_one
        (hsq.symm.trans (orderOf_dvd_iff_pow_eq_one.mp hd))
    have horder : orderOf (a*b) = 4 := by
      interval_cases ho : orderOf (a*b) <;> simp_all
    exact ⟨(a, b), r.one_class z hz a haZ, p.property.1, by
      simpa only [halfOrder_def, horder, Nat.reduceDiv] using hsq⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ResidualFiberDisplacement

/-- The actual distinguished Thompson fiber is counted by displacements in A.
Its first factors include all of A; the nonidentity target excludes a = 1. -/
public theorem proper_residualGenerated_kappa_distinguished_eq_displacement_pairs
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t u : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    kappa z u z = Nat.card (ResidualDistinguishedDisplacementPairs Z M z u) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hZA, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  have hk : kappa z u z = Nat.card (Fiber z u z) := by
    simp only [kappa_def, Fiber, halfOrder_def]
  rw [hk]
  exact Nat.card_congr (ResidualFiberDisplacement.fiber_equiv_displacement_pairs
    h.disconnected r hZA hz hzM hu
    (not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM huD))

end BenderSuzuki.ZD
