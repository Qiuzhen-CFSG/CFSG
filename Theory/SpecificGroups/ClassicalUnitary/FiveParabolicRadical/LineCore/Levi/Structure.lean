module

public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Theory.PGroupCore
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.IsPerfect

/-!
# The identity-form SU₃ group over the field of sixteen elements

The natural map to PSU₃ is an isomorphism: a scalar in its kernel has both
cube and fifth power equal to one. Huppert II.10.13 then gives simplicity.
Two coordinate interchanges do not commute, so the group is perfect; its
normal two-core is trivial because a nontrivial finite perfect group cannot
be a two-group.

Source: Huppert, *Endliche Gruppen I*, II.10.13; the SU₃(4) Levi factor in
Aschbacher--Smith, F.1.12(7), printed p.263.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Levi
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

noncomputable def project : J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _
    (fun x => Subgroup.mem_map_of_mem _ x.property)

theorem project_surjective : Function.Surjective (project J) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem project_injective (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4) : Function.Injective (project J) := by
  apply (project J).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxproj : ProjGenLinGroup.mk (x : GL (Fin 3) F) = 1 :=
    congrArg Subtype.val hx
  have hxc := ProjGenLinGroup.mk_eq_one.mp hxproj
  rw [GeneralLinearGroup.center_eq_range_scalar] at hxc
  obtain ⟨k, hk⟩ := hxc
  have hs := (J.mem_specialSubgroup_iff (x : GL (Fin 3) F)).mp x.property
  rw [← hk] at hs
  have hu := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 0) hs.1
  have hn : J.conj (k : F) * (k : F) = 1 := by
    simpa [hJ, HermitianForm.conjTranspose, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three] using hu
  have hd := congrArg (fun a : Fˣ => (a : F)) hs.2
  have h3 : (k : F) ^ 3 = 1 := by
    simpa [GeneralLinearGroup.det, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_fin_three, pow_succ, pow_two] using hd
  have h5 : (k : F) ^ 5 = 1 := by simpa [hconj, pow_succ] using hn
  have hk1 : (k : F) = 1 := by
    have h6 : (k : F) ^ 6 = 1 := by rw [show 6 = 3 * 2 by decide, pow_mul, h3, one_pow]
    rw [show 6 = 5 + 1 by decide, pow_succ, h5, one_mul] at h6
    exact h6
  have hkunit : k = 1 := Units.ext hk1
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  change (x : GL (Fin 3) F) = 1
  rw [← hk, hkunit, map_one]

noncomputable def projectEquiv (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective (project J) ⟨project_injective J hJ hconj, project_surjective J⟩

private def swap01 : GL (Fin 3) F where
  val := !![0,1,0;1,0,0;0,0,1]
  inv := !![0,1,0;1,0,0;0,0,1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def swap12 : GL (Fin 3) F where
  val := !![1,0,0;0,0,1;0,1,0]
  inv := !![1,0,0;0,0,1;0,1,0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap01_mem [CharP F 2] (hJ : J.form = 1) :
    swap01 (F := F) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap01, hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]
  · apply Units.ext
    simp [swap01, GeneralLinearGroup.det, Matrix.det_fin_three, CharTwo.neg_eq]

private theorem swap12_mem [CharP F 2] (hJ : J.form = 1) :
    swap12 (F := F) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap12, hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]
  · apply Units.ext
    simp [swap12, GeneralLinearGroup.det, Matrix.det_fin_three, CharTwo.neg_eq]

theorem not_commutative [CharP F 2] (hJ : J.form = 1) :
    ¬ IsMulCommutative J.specialSubgroup := by
  intro hc
  let := hc
  let a : J.specialSubgroup := ⟨swap01, swap01_mem J hJ⟩
  let b : J.specialSubgroup := ⟨swap12, swap12_mem J hJ⟩
  have hab : a * b = b * a := mul_comm' a b
  have h := congrArg (fun x : J.specialSubgroup => (x.val : Matrix (Fin 3) (Fin 3) F) 0 1) hab
  simp [a, b, swap01, swap12, Matrix.mul_apply, Fin.sum_univ_three] at h

theorem simple [Finite F] (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (hcard : Nat.card F = 16) (hfixed : Nat.card {x : F // J.conj x = x} = 4) :
    IsSimpleGroup J.specialSubgroup := by
  have hs := BenderSuzuki.External.huppert_II_10_13 J 4 (by decide) hcard hfixed
  exact (projectEquiv J hJ hconj).isSimpleGroup_congr.mpr hs

theorem perfect [Finite F] [CharP F 2] (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (hcard : Nat.card F = 16) (hfixed : Nat.card {x : F // J.conj x = x} = 4) :
    Group.IsPerfect J.specialSubgroup := by
  let := simple J hJ hconj hcard hfixed
  constructor
  rcases (inferInstance : (commutator J.specialSubgroup).Normal).eq_bot_or_eq_top with h | h
  · exact False.elim (not_commutative J hJ ((commutator_eq_bot_iff _).mp h))
  · exact h

theorem twoCore [Finite F] [CharP F 2] (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (hcard : Nat.card F = 16) (hfixed : Nat.card {x : F // J.conj x = x} = 4) :
    pCore 2 J.specialSubgroup = ⊥ := by
  let : Finite (GL (Fin 3) F) := Finite.of_injective Units.val Units.val_injective
  let := simple J hJ hconj hcard hfixed
  let := perfect J hJ hconj hcard hfixed
  rcases (inferInstance : (pCore 2 J.specialSubgroup).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup J.specialSubgroup) := h ▸ pCore_isPGroup
    have hpG : IsPGroup 2 J.specialSubgroup := hp.of_equiv (Subgroup.topEquiv)
    exact False.elim (Group.IsPerfect.not_isNilpotent J.specialSubgroup hpG.isNilpotent)
end Theory.SpecificGroups.UnitaryFive.LineCore.Levi
