module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootSylow
public import Theory.GroupTheory.PGroup.OrderTwentySevenNormalForm
public import Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion

/-!
# The ternary unitary Sylow pair and perfect central kernels

In characteristic three the centered Hermitian root at `a` has coordinates
`(a, a * conj a)`. It cubes to one and the actual torus element at minus one
inverts it. First coordinates one and an element outside the fixed field give
noncommuting roots. They generate the actual Sylow subgroup of order 27;
the same torus element fixes their central commutator. Simultaneous inversion
therefore excludes three from every finite perfect central-cover kernel.

Source: Huppert II.10.12 for the literal root and torus maps; the PSU₃(3)
case of Aschbacher–Smith I.1.3, used in B.5.7.
-/

noncomputable section
open Matrix Subgroup BenderSuzuki.External
open scoped commutatorElement
namespace BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectKernels
open OddPrimeSylow.NormalizedOuter.Coverage

variable {F : Type*} [Field F] [CharP F 3] (J : HermitianForm 3 F)

private def centered (a : F) : hermitianUnipotentCoord J :=
  ⟨(a, a * J.conj a), by
    dsimp only
    rw [map_mul, J.conj_involutive]
    have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    linear_combination (a * J.conj a) * h3⟩

private theorem centered_cube (a : F) : centered J a ^ 3 = 1 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  rw [pow_succ, pow_two]
  apply Subtype.ext
  apply Prod.ext
  · change (a + a) + a = 0
    linear_combination a * h3
  · change (a * J.conj a + a * J.conj a - a * J.conj a) +
      a * J.conj a - (a + a) * J.conj a = 0
    ring

private theorem centered_inverted (a : F) :
    hermitianTorusAction J (-1) (centered J a) = (centered J a)⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [hermitianTorusAction_fst, Units.val_neg, Units.val_one,
      map_neg, map_one, inv_neg, inv_one, neg_one_sq, mul_one, mul_neg_one]
    rfl
  · simp only [hermitianTorusAction_snd, Units.val_neg, Units.val_one,
      map_neg, map_one, inv_neg, inv_one, mul_neg_one, neg_neg]
    change a * J.conj a = J.conj (a * J.conj a)
    rw [map_mul, J.conj_involutive, mul_comm]

omit [CharP F 3] in
private theorem zero_first_central (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    z ∈ center (hermitianUnipotentCoord J) := by
  apply mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 + z.val.1 = z.val.1 + w.val.1
    exact add_comm _ _
  · change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
      z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1
    simp [hz, add_comm]

omit [CharP F 3] in
private theorem zero_first_fixed (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    hermitianTorusAction J (-1) z = z := by
  apply Subtype.ext
  apply Prod.ext
  · simp [hermitianTorusAction_fst, hz]
  · simp [hermitianTorusAction_snd]

omit [CharP F 3] in
private theorem exists_moved [Finite F]
    (hcard : Nat.card F = 3 ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 3) :
    ∃ a : F, J.conj a ≠ a := by
  by_contra! hall
  let e : {x : F // J.conj x = x} ≃ F :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hall x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := hfixed.symm.trans ((Nat.card_congr e).trans hcard)
  norm_num at h

/-- The actual standard-form PSU₃(3) root Sylow and its sign torus element
exclude three from every finite perfect central-cover kernel. All local
generation, order, centrality and simultaneous-inversion hypotheses are
constructed from the field cardinalities. -/
public theorem not_three_dvd_kernel_standard [Finite F]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card F = 3 ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 3)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  obtain ⟨a, ha⟩ := exists_moved J hcard hfixed
  let x := centered J 1
  let y := centered J a
  have hxy : x * y ≠ y * x := by
    intro he
    apply ha
    have hh := congrArg (fun z : hermitianUnipotentCoord J => z.val.2) he
    change 1 * J.conj 1 + a * J.conj a - 1 * J.conj a =
      a * J.conj a + 1 * J.conj 1 - a * J.conj 1 at hh
    simp only [map_one, mul_one, one_mul] at hh
    linear_combination -hh
  have hc : Nat.card (hermitianUnipotentCoord J) = 27 :=
    (Nat.card_congr (MonoidHom.ofInjective (root_injective J hJ)).toEquiv).trans
      (rootGroup_card J hJ 3 hcard hfixed)
  have hgen : closure ({x, y} : Set (hermitianUnipotentCoord J)) = ⊤ := by
    let C := closure ({x, y} : Set (hermitianUnipotentCoord J))
    let xC : C := ⟨x, subset_closure (by simp)⟩
    let yC : C := ⟨y, subset_closure (by simp)⟩
    exact OrderTwentySeven.subgroup_eq_top_of_noncommuting hc C xC yC
      (fun h => hxy (congrArg Subtype.val h))
  have hgen_image : closure ({root J hJ x, root J hJ y} :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) = rootGroup J hJ := by
    have hh := congrArg (Subgroup.map (root J hJ)) hgen
    simpa only [rootGroup, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      ← MonoidHom.range_eq_map] using hh
  have hz0 : (⁅x, y⁆ : hermitianUnipotentCoord J).val.1 = 0 := by
    rw [hermitianUnipotent_commutator]
  have hz := zero_first_central J ⁅x,y⁆ hz0
  have hinv (b : F) : hermitianTorusPSU J hJ (-1) * root J hJ (centered J b) *
      (hermitianTorusPSU J hJ (-1))⁻¹ = (root J hJ (centered J b))⁻¹ := by
    rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right,
      centered_inverted, map_inv]
  have hfix : Commute (hermitianTorusPSU J hJ (-1))
      ⁅root J hJ x, root J hJ y⁆ := by
    rw [← map_commutatorElement]
    change hermitianTorusPSU J hJ (-1) * root J hJ ⁅x,y⁆ =
      root J hJ ⁅x,y⁆ * hermitianTorusPSU J hJ (-1)
    rw [hermitianTorusPSU_mul_unipotent, zero_first_fixed J _ hz0]
  exact PerfectCentralCovering.not_dvd_card_kernel_of_simultaneous_inversion
    f.toMonoidHom f.surjective f.ker_le_center (by decide)
    (rootSylow J hJ Nat.prime_three hcard hfixed)
    (root J hJ x) (root J hJ y) (hermitianTorusPSU J hJ (-1))
    (by simpa only [rootSylow_coe] using hgen_image)
    (by rw [← map_pow, centered_cube, map_one])
    (by rw [← map_pow, centered_cube, map_one])
    (by
      rw [← map_commutatorElement, ← (root J hJ).map_one]
      exact (root_injective J hJ).ne (fun h => hxy
        (commutatorElement_eq_one_iff_mul_comm.mp h)))
    (by
      rw [← map_commutatorElement]
      exact (show Commute x ⁅x,y⁆ from mem_center_iff.mp hz x).map (root J hJ))
    (by
      rw [← map_commutatorElement]
      exact (show Commute y ⁅x,y⁆ from mem_center_iff.mp hz y).map (root J hJ))
    (hinv 1) (hinv a) hfix

end BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectKernels
