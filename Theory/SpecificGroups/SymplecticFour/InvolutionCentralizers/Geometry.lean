module

public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics

/-!
# Proper parabolics containing symplectic involution centralizers

The centralizer preserves the nonzero isotropic moved space. An actual
symplectic change of basis identifies its stabilizer with a conjugate point
or plane parabolic. A commutator of two of the existing root matrices moves
the standard point and plane. Normality of the derived group then proves
that intersection with any such parabolic is proper in the derived carrier,
including over the field of two elements.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 16.1.4(1), printed p.1171. The geometric containment in fact applies
to all three involution types.
-/

public noncomputable section
open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open InvolutionTypes TwoLocalCover
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

theorem movedSpace_stabilizer_parabolic (g : Sp F) (hg : orderOf g = 2) :
    IsParabolic (stabilizer (movedSpace g)) := by
  obtain ⟨h, hh⟩ := isotropic_subspace_conjugate_standard (movedSpace g)
    (movedSpace_ne_bot g (orderOf_eq_prime_iff.mp hg).2)
    (movedSpace_isotropic g (orderOf_eq_prime_iff.mp hg).1)
  have hstab : stabilizer (movedSpace g) =
      (stabilizer ((movedSpace g).map (toLinear h).toLinearMap)).map
        (MulAut.conj h⁻¹).toMonoidHom := by
    ext c
    constructor
    · intro hc
      refine ⟨h * c * h⁻¹, ?_, by simp [mul_assoc]⟩
      have hc := (mem_stabilizer_iff _ _).mp hc
      apply (mem_stabilizer_iff _ _).mpr
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨c • x, hc x hx, ?_⟩
      change h • (c • x) = (h * c * h⁻¹) • (h • x)
      simp only [mul_smul, inv_smul_smul]
    · rintro ⟨c, hc, rfl⟩
      have hc := (mem_stabilizer_iff _ _).mp hc
      apply (mem_stabilizer_iff _ _).mpr
      intro x hx
      obtain ⟨y, hy, he⟩ := hc (h • x) ⟨x, hx, rfl⟩
      change h • y = c • (h • x) at he
      have he' := congrArg (h⁻¹ • ·) he
      simp only [inv_smul_smul] at he'
      change (h⁻¹ * c * (h⁻¹)⁻¹) • x ∈ movedSpace g
      simpa only [inv_inv, mul_smul, ← he'] using (show y ∈ movedSpace g from hy)
  refine ⟨h⁻¹, ?_⟩
  rcases hh with hh | hh
  · exact Or.inl (by simpa only [hh, pointParabolic] using hstab)
  · exact Or.inr (by simpa only [hh, planeParabolic] using hstab)

omit [CharP F 2] in
theorem parabolic_ne_top (P : Subgroup (Sp F)) (hP : IsParabolic P) : P ≠ ⊤ := by
  obtain ⟨h, rfl | rfl⟩ := hP
  · intro he
    apply pointParabolic_ne_top (F := F)
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    simpa using he
  · intro he
    apply planeParabolic_ne_top (F := F)
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    simpa using he

private theorem commutator_moves_point :
    ∃ d : Sp F, d ∈ commutator (Sp F) ∧
      d.val (.inr 1) (.inl 0) ≠ 0 := by
  let u : Sp F := rootElement 1 1
  let v : Sp F := rootElement 6 1
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa only [← pow_two] using rootElement_sq 1 (1 : F))
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [← pow_two] using rootElement_sq 6 (1 : F))
  refine ⟨⁅u,v⁆, commutator_mem_commutator (mem_top _) (mem_top _), ?_⟩
  rw [commutatorElement_def, hu, hv]
  change (rootMatrix 1 (1 : F) * rootMatrix 6 1 * rootMatrix 1 1 * rootMatrix 6 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (.inr 1) (.inl 0) ≠ 0
  simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.single]

theorem derived_not_le_point : ¬ commutator (Sp F) ≤ pointParabolic := by
  obtain ⟨d, hd, hentry⟩ := commutator_moves_point (F := F)
  intro h
  exact hentry (((mem_pointParabolic_iff d).mp (h hd)).2 1)

theorem derived_not_le_plane : ¬ commutator (Sp F) ≤ planeParabolic := by
  obtain ⟨d, hd, hentry⟩ := commutator_moves_point (F := F)
  intro h
  exact hentry ((mem_planeParabolic_iff d).mp (h hd) 1 0)

theorem derived_not_le_parabolic (P : Subgroup (Sp F)) (hP : IsParabolic P) :
    ¬ commutator (Sp F) ≤ P := by
  have hmove (H : Subgroup (Sp F)) (h : Sp F)
      (hle : commutator (Sp F) ≤ H.map (MulAut.conj h).toMonoidHom) :
      commutator (Sp F) ≤ H := by
    intro d hd
    have hd' : h * d * h⁻¹ ∈ commutator (Sp F) :=
      (inferInstance : (commutator (Sp F)).Normal).conj_mem d hd h
    obtain ⟨x, hx, he⟩ := hle hd'
    have hx' : x = d := (MulAut.conj h).injective he
    simpa only [hx'] using (show x ∈ H from hx)
  obtain ⟨h, rfl | rfl⟩ := hP
  · exact fun hle => derived_not_le_point (hmove _ h hle)
  · exact fun hle => derived_not_le_plane (hmove _ h hle)

theorem derived_parabolic_ne_top (P : Subgroup (Sp F)) (hP : IsParabolic P) :
    P.subgroupOf (commutator (Sp F)) ≠ ⊤ := by
  intro he
  apply derived_not_le_parabolic P hP
  intro d hd
  have hm : (⟨d, hd⟩ : commutator (Sp F)) ∈ P.subgroupOf (commutator (Sp F)) := by
    rw [he]; trivial
  exact hm


end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
