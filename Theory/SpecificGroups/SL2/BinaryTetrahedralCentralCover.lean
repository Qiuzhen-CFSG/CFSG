module
public import Theory.SpecificGroups.SL2.BinaryTetrahedralHom
public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient
public import Theory.SpecificGroups.Quaternion.CentralTwoOrbit
public import Theory.GroupTheory.CentralCoprimeLift
public import Theory.GroupTheory.NoSectionInjectivity

/-!
# Nonsplit central two-covers of the tetrahedral quotient

A nonsplit surjection onto the center quotient of the actual binary
tetrahedral group, with central two-group kernel, contains an embedded
binary tetrahedral group surjecting onto that quotient. The kernel may
have arbitrary order; no cyclicity or finiteness assumption is needed.

Lift the order-three generator with cube one by the coprime kernel power
map. Its commutator orbit gives quaternion generators with the correct
action, hence a binary tetrahedral homomorphism. Its quotient composite
is the standard projection preceded by conjugation by the square of the
order-three generator. This composite has kernel of order two, and the
absence of a section forces the original homomorphism to be injective.

This is the elementary arbitrary-kernel realization of the q=3 Schur-cover
step used in ABG II.3 Proposition 2, article p.22. The explicit finite model
is the extracted GLS3 5.2.4 binary tetrahedral matrix group.
-/

namespace GLS3.Chapter5.SchurPresentation

public theorem exists_binaryTetrahedral_embedding_of_nonsplit
    {E : Type*} [Group E]
    (q : E →* BinaryTetrahedralCentralQuotient) (hq : Function.Surjective q)
    (hcenter : q.ker ≤ Subgroup.center E) (hker : IsPGroup 2 q.ker)
    (hnosection : ¬ ∃ s : BinaryTetrahedralCentralQuotient →* E,
      q.comp s = MonoidHom.id _) :
    ∃ f : BinaryTetrahedral →* E, Function.Injective f ∧
      Function.Surjective (q.comp f) ∧ Nat.card (q.comp f).ker = 2 := by
  let : Finite BinaryTetrahedral :=
    Finite.of_equiv SL23 binaryTetrahedralEquivSL.toEquiv.symm
  let pi := QuotientGroup.mk' (Subgroup.center BinaryTetrahedral)
  obtain ⟨t, htq, ht⟩ := q.exists_pow_eq_one_lift_of_central_pgroup_ker hq
    hcenter hker (by decide : Nat.Coprime 2 3) (pi binaryT)
    (by rw [← map_pow, binaryT_cube, map_one])
  obtain ⟨x, hx⟩ := hq (pi binaryI)
  let a := x⁻¹ * t * x * t⁻¹
  let b := (t * a * t⁻¹) * a⁻¹
  have hqa : q a = pi (binaryI⁻¹ * binaryT * binaryI * binaryT⁻¹) := by
    simp only [a, map_mul, map_inv, hx, htq]
  have hs : a ^ 2 ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, hqa, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr binary_commutator_square_central
  obtain ⟨ha4, hb2, hba, hta, htb⟩ :=
    QuaternionGroup.relations_of_central_two_orbit q.ker hcenter hker x t ht hs
  obtain ⟨f, hfI, hfJ, hfT⟩ := exists_binaryTetrahedral_hom a b t
    ha4 hb2 hba ht hta htb
  have hcomp : q.comp f = pi.comp (MulAut.conj (binaryT ^ 2)).toMonoidHom := by
    apply binary_hom_ext
    · change q (f binaryI) = pi (binaryT ^ 2 * binaryI * (binaryT ^ 2)⁻¹)
      rw [hfI, hqa, binary_commutator_eq_conjugate]
    · change q (f binaryJ) = pi (binaryT ^ 2 * binaryJ * (binaryT ^ 2)⁻¹)
      rw [hfJ]
      change q ((t * a * t⁻¹) * a⁻¹) = _
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, htq, hqa]
      simpa only [map_mul, map_inv] using congrArg pi binary_commutator_pair_eq_conjugate
    · change q (f binaryT) = pi (binaryT ^ 2 * binaryT * (binaryT ^ 2)⁻¹)
      rw [hfT, htq]
      rw [show binaryT ^ 2 * binaryT * (binaryT ^ 2)⁻¹ = binaryT by group]
  have hsurj : Function.Surjective (q.comp f) := by
    rw [hcomp]
    exact (QuotientGroup.mk'_surjective _).comp (MulAut.conj (binaryT ^ 2)).surjective
  have hcard : Nat.card (q.comp f).ker = 2 := by
    have h := (q.comp f).ker.card_mul_index
    rw [Subgroup.index_ker] at h
    have hr : Nat.card (q.comp f).range = Nat.card BinaryTetrahedralCentralQuotient := by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hr, binaryTetrahedral_quotient_card, binaryTetrahedral_card] at h
    omega
  exact ⟨f, q.injective_of_comp_ker_card_two_of_no_section f hsurj hcard hnosection,
    hsurj, hcard⟩

end GLS3.Chapter5.SchurPresentation
