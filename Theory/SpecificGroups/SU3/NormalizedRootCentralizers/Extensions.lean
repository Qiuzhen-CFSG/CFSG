module

public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers
public import Theory.SpecificGroups.SU3.ExtensionBorel
/-!
# Root centralizers in diagonal unitary extensions

A triangular unitary actor fixes a nonzero central root precisely when
its first and last diagonal entries agree. Projective commutation lifts
without a scalar error, by comparison of the first diagonal entry. It then
fixes every central root. This proves uniform rigidity in the actual PGU
matrix Borel and in every inner-diagonal actor Borel.

The latter calculation applies to the commutator-generated residual in
A.3.18's nonsplit extension after `ResidualAction` removes its field part.
It does not assert rigidity for arbitrary field automorphisms.

Source: Aschbacher–Smith, A.3.16–18 and proof of 13.6.6, printed p.927.
-/

public section
open Subgroup Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers
open BorelTorus BorelTorus.EvenCenterAction ExtensionBorel
variable {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

theorem upper_fixes_all_central (u : J.unitarySubgroup) (hu : u ∈ upperUnitary J)
    (b : Multiplicative (fixedField J)) (hb : b.toAdd ≠ 0)
    (hfix : J.unitaryConj u (centralMap J hJ b) = centralMap J hJ b) :
    ∀ c : Multiplicative (fixedField J),
      J.unitaryConj u (centralMap J hJ c) = centralMap J hJ c := by
  have hz1 (c : Multiplicative (fixedField J)) : (centralCoord J c).val.1 = 0 := rfl
  have hz2 (c : Multiplicative (fixedField J)) : (centralCoord J c).val.2 = c.toAdd := rfl
  have h10 : u.val.val 1 0 = 0 := hu (by decide)
  have h20 : u.val.val 2 0 = 0 := hu (by decide)
  have h21 : u.val.val 2 1 = 0 := hu (by decide)
  have hu00 : u.val.val 0 0 ≠ 0 := by
    have he := (J.mem_unitarySubgroup_iff _).mp u.property
    rw [hJ] at he
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 0) he
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20] at hh
    exact right_ne_zero_of_mul_eq_one hh
  have hp := congrArg Subtype.val hfix
  rw [J.unitaryConj_apply_val] at hp
  have hmul := mul_inv_eq_iff_eq_mul.mp hp
  change ProjGenLinGroup.mk u.val * ProjGenLinGroup.mk (hermitianUnipotentGL J (centralCoord J b)) =
    ProjGenLinGroup.mk (hermitianUnipotentGL J (centralCoord J b)) * ProjGenLinGroup.mk u.val at hmul
  rw [← map_mul, ← map_mul] at hmul
  obtain ⟨k, hk⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmul
  have hk1 : k = 1 := by
    apply Units.ext
    apply mul_left_cancel₀ hu00
    have hh := congrArg (fun M : GL (Fin 3) E => M.val 0 0) hk
    simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal,
      hermitianUnipotentGL, hermitianUnipotentMatrix, hz1, hz2,
      Matrix.mul_apply, Fin.sum_univ_three, h20] using hh
  rw [hk1, map_one, mul_one] at hk
  have hdiag : u.val.val 0 0 = u.val.val 2 2 := by
    have hb' : (b.toAdd : E) ≠ 0 := fun he => hb (Subtype.ext he)
    apply mul_right_cancel₀ hb'
    have hh := congrArg (fun M : GL (Fin 3) E => M.val 0 2) hk
    have hh' : u.val.val 0 0 * (b.toAdd : E) + u.val.val 0 2 =
        u.val.val 0 2 + (b.toAdd : E) * u.val.val 2 2 := by
      simpa [hermitianUnipotentGL, hermitianUnipotentMatrix, hz1, hz2,
        Matrix.mul_apply, Fin.sum_univ_three] using hh
    linear_combination hh'
  intro c
  apply Subtype.ext
  rw [J.unitaryConj_apply_val]
  apply mul_inv_eq_iff_eq_mul.mpr
  change ProjGenLinGroup.mk u.val * ProjGenLinGroup.mk (hermitianUnipotentGL J (centralCoord J c)) =
    ProjGenLinGroup.mk (hermitianUnipotentGL J (centralCoord J c)) * ProjGenLinGroup.mk u.val
  rw [← map_mul, ← map_mul]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentGL, hermitianUnipotentMatrix, hz1, hz2,
      Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, hdiag, mul_comm, add_comm]

omit [CharP E 2] in
private theorem pgu_commute_iff (u : J.unitarySubgroup)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    unitaryToPGU J u * componentInPGU J x = componentInPGU J x * unitaryToPGU J u ↔
      J.unitaryConj u x = x := by
  constructor
  · intro h
    apply Subtype.ext
    rw [J.unitaryConj_apply_val]
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    rw [J.unitaryConj_apply_val] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

variable [Finite E] {n : ℕ} (hn : 1 < n)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)

include hn hcard hfixed in
/-- Uniform centralizers in the actual PGU Borel, with the original component inclusion. -/
theorem pgu_uniform (r : projectiveUnitary J)
    (hr : r ∈ (center (pguRoot J hJ)).map (pguRoot J hJ).subtype) (hne : r ≠ 1) :
    pguBorel J ⊓ centralizer ({r} : Set _) =
      pguBorel J ⊓ centralizer
        (((center (pguRoot J hJ)).map (pguRoot J hJ).subtype : Subgroup _) : Set _) := by
  have hcenter : (center (pguRoot J hJ)).map (pguRoot J hJ).subtype =
      (centralImage J hJ).map (componentInPGU J) := by
    rw [pguRoot, ← map_embeddedCenter _ _ (componentInPGU_injective J),
      root_center J hn hcard hfixed hJ]
  rw [hcenter] at hr ⊢
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hr
  have hb : b.toAdd ≠ 0 := fun he => hne (by rw [show b = 1 from he, map_one, map_one])
  apply le_antisymm
  · rintro g ⟨⟨u, hu, rfl⟩, hc⟩
    have hfix := (pgu_commute_iff J u _).mp (mem_centralizer_singleton_iff.mp hc)
    refine ⟨⟨u, hu, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ((pgu_commute_iff J u _).mpr (upper_fixes_all_central J hJ u hu b hb hfix c)).symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
      ⟨_, ⟨b, rfl⟩, rfl⟩))

include hJ hcard hfixed in
/-- Triangular inner-diagonal actors fixing one nonzero root coordinate fix all of them. -/
theorem unitary_actor_fixes_all (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ∈ actorBorel J hJ) (hd : a ∈ J.unitaryConjHom.range)
    (b : Multiplicative (fixedField J)) (hb : b.toAdd ≠ 0)
    (hfix : a (centralMap J hJ b) = centralMap J hJ b) :
    ∀ c : Multiplicative (fixedField J), a (centralMap J hJ c) = centralMap J hJ c := by
  obtain ⟨u, rfl⟩ := hd
  rw [J.unitaryConjHom_apply] at ha hfix ⊢
  have hu : u ∈ upperUnitary J := by
    apply (root_map_eq_iff_upper J hJ hcard hfixed _ 1 u ?_).mp
      (actorBorel_preserves_root J hJ _ ha)
    intro x
    change (J.unitaryConj u x).val = _ * ProjGenLinGroup.map (RingHom.id E) _ * _
    rw [ProjGenLinGroup.map_id, MonoidHom.id_apply]
    exact J.unitaryConj_apply_val u x
  exact upper_fixes_all_central J hJ u hu b hb hfix

private theorem commute_conj_iff {M : Type*} [Group M]
    (hi : Function.Injective (MulAut.conj : M →* MulAut M)) (a : MulAut M) (x : M) :
    a * MulAut.conj x = MulAut.conj x * a ↔ a x = x := by
  have he : a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by
    ext y
    simp
  constructor
  · intro h
    apply hi
    rw [← he, h, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    apply mul_inv_eq_iff_eq_mul.mp
    rw [he, h]

include hn hcard hfixed in
/-- Uniform rigidity in any Borel subgroup of inner-diagonal actors.
The full semilinear Borel is intentionally not asserted to have this property. -/
theorem actor_uniform (B : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hB : B ≤ actorBorel J hJ) (hD : B ≤ J.unitaryConjHom.range)
    (r : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hr : r ∈ (centralImage J hJ).map MulAut.conj) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set _) =
      B ⊓ centralizer ((centralImage J hJ).map MulAut.conj : Set _) := by
  have hi := binary_inner_injective J hJ hn hcard
    (huppert_II_10_4_conj_eq_frobenius J (2^n) hcard hfixed)
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hr
  have hb : b.toAdd ≠ 0 := fun he => hne (by rw [show b = 1 from he, map_one, map_one])
  apply le_antisymm
  · rintro a ⟨ha, hc⟩
    have hfix := (commute_conj_iff hi a _).mp (mem_centralizer_singleton_iff.mp hc)
    refine ⟨ha, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ((commute_conj_iff hi a _).mpr
      (unitary_actor_fixes_all J hJ hcard hfixed a (hB ha) (hD ha) b hb hfix c)).symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
      ⟨_, ⟨b, rfl⟩, rfl⟩))

end BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers
