module

public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.GroupTheory.CentralizerEquivBounds

/-!
# Transport of SU₃ involution-centralizer maximality

The actual map SU₃ → PSU₃ has a central kernel of exponent three. Cubing a
lift produces an involution, and its whole centralizer maps onto the quotient
centralizer. Since the scalar kernel lies inside that centralizer, the subgroup
correspondence descends maximality. Special-unitary conjugacy reduces every
involution to `diag(-1,-1,1)` over the finite quadratic field, including p = 3.

The final restriction lemma identifies the intrinsic centralizer with the
literal ambient centralizer restricted to L; it asserts no ambient maximality.
These are transport results, conditional on standard-centralizer maximality.

Source: Aschbacher--Smith, A.3.21(a), printed p.55, and its use in E.1.14(7),
printed p.214. The scalar-kernel and eigenbasis calculations are reused from
the actual SU₃ model, without replacing its image in PGL by another carrier.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality

private theorem coatom_map_of_ker_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (C : Subgroup G)
    (hk : f.ker ≤ C) (hC : IsCoatom C) : IsCoatom (C.map f) := by
  have hcomap : (C.map f).comap f = C := by
    rw [comap_map_eq, sup_eq_left.mpr hk]
  refine ⟨?_, ?_⟩
  · intro h
    apply hC.1
    rw [← hcomap, h, comap_top]
  · intro M hM
    have hc : C < M.comap f := by
      rw [← hcomap]
      exact (comap_lt_comap_of_surjective hf).mpr hM
    have ht := hC.2 (M.comap f) hc
    apply comap_injective hf
    simpa only [comap_top] using ht

/-- The central cubic quotient preserves involution-centralizer maximality. -/
theorem projective_centralizer_isCoatom_of_special
    {F : Type*} [Field F] (J : HermitianForm 3 F)
    (z : J.specialSubgroup) (hz : z ^ 2 = 1)
    (hmax : IsCoatom (centralizer ({z} : Set J.specialSubgroup))) :
    IsCoatom (centralizer ({J.specialToProjective z} :
      Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  have hcube : ∀ x ∈ J.specialToProjective.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x, hx⟩)
  rw [← SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel
    J.specialToProjective J.specialToProjective_surjective
    J.specialToProjective_ker_le_center hcube z hz]
  exact coatom_map_of_ker_le J.specialToProjective J.specialToProjective_surjective
    _ (J.specialToProjective_ker_le_center.trans (center_le_centralizer _)) hmax

/-- One standard SU₃ centralizer supplies every projective involution centralizer. -/
theorem projective_centralizer_isCoatom_of_standard
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (hc : ∀ x, J.conj x = x ^ p)
    (hmax : IsCoatom (centralizer ({SU3.standardInvolution J hJ} :
      Set J.specialSubgroup)))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    IsCoatom (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  have hcube : ∀ x ∈ J.specialToProjective.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel
    J.specialToProjective J.specialToProjective_surjective hcube t ht
  obtain ⟨g, hg⟩ := SU3.exists_special_involution_conjugator hp hcard J hJ hc z hz
  have hconj := (isCoatom_centralizer_equiv_iff (MulAut.conj g)
    (SU3.standardInvolution J hJ)).mpr hmax
  change IsCoatom (centralizer ({g * SU3.standardInvolution J hJ * g⁻¹} :
    Set J.specialSubgroup)) at hconj
  rw [hg] at hconj
  exact projective_centralizer_isCoatom_of_special J z
    (hz ▸ pow_orderOf_eq_one z) hconj

/-- Restricting the ambient centralizer is exactly the intrinsic centralizer. -/
theorem ambient_centralizer_subgroupOf_eq {G : Type*} [Group G]
    (L : Subgroup G) (z : G) (hzL : z ∈ L) :
    (centralizer ({z} : Set G)).subgroupOf L =
      centralizer ({(⟨z, hzL⟩ : L)} : Set L) := by
  ext x
  simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

/-- The literal ambient adapter uses only order in the subgroup, not ambient maximality. -/
theorem ambient_centralizer_isCoatom_of_intrinsic {G : Type*} [Group G]
    (L : Subgroup G) (z : G) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hmax : ∀ t : L, orderOf t = 2 → IsCoatom (centralizer ({t} : Set L))) :
    IsCoatom ((centralizer ({z} : Set G)).subgroupOf L) := by
  rw [ambient_centralizer_subgroupOf_eq L z hzL]
  apply hmax
  rw [← orderOf_injective L.subtype Subtype.val_injective]
  exact hz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality
