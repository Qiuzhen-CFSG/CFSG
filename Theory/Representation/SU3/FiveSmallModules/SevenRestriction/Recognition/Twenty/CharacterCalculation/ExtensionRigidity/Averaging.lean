module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.LocalInputs

/-!
# Linear equations for the degree-twenty Weyl operator

If the root center has no fixed vectors, its norm operator is zero. Multiply
this identity on both sides by the Weyl action, and apply the SU Bruhat
identity separately to the nonidentity elements in each root-center coset.
The resulting equations are linear in the Weyl operator; their coefficients
use only the root and torus actions. Their right sides are independent of
the representation.

This module proves those equations and their comparison for two actions
with the same Borel restriction. Injectivity of the resulting linear
operator is a separate calculation, specified in `ExtensionRigidity.Inputs`.
The extension-rigidity consumer discharges the remaining generation and
coordinate-transport steps once that injectivity is supplied.

Source: the matrix calculation of Huppert II.10.12, as formalized in
`BenderSuzuki.External.hermitianWeylPSU_mul_unipotent_mul_weyl`. Its internal
GL identity is proved here in SU itself; no projective relation is applied
to an undescended representation. The matrix field may have odd characteristic.
Application: Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
pp.10–11; that passage is motivation, not a certificate of injectivity.
-/

@[expose] public section

open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private theorem root_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z t he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : J.specialSubgroup => x.val.val 0 1) he
  · exact congrArg (fun x : J.specialSubgroup => x.val.val 0 2) he

private noncomputable def rootEquiv : hermitianUnipotentCoord J ≃* specialRoot J hJ :=
  MulEquiv.ofBijective (hermitianUnipotentSU J hJ).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (root_injective J hJ),
      (hermitianUnipotentSU J hJ).rangeRestrict_surjective⟩

private theorem coord_eq_one (z : hermitianUnipotentCoord J) (hz : z.val.2 = 0) : z = 1 := by
  have ha : z.val.1 = 0 := by
    have h := z.property
    rw [hz, map_zero, zero_add, zero_add] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact (map_eq_zero J.conj).mp h
  apply Subtype.ext
  exact Prod.ext ha hz

private theorem weyl_square : hermitianWeylSU J hJ * hermitianWeylSU J hJ = 1 := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro i j
  change (hermitianWeylMatrix * hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) F) i j = (1 : Matrix (Fin 3) (Fin 3) F) i j
  fin_cases i <;> fin_cases j <;> simp [hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- The Bruhat relation holds already in SU, with no matrix-characteristic restriction. -/
theorem special_weyl_mul_root_mul_weyl (z : hermitianUnipotentCoord J) (hz : z.1.2 ≠ 0) :
    hermitianWeylSU J hJ * hermitianUnipotentSU J hJ z * hermitianWeylSU J hJ =
      hermitianUnipotentSU J hJ (hermitianBruhatLeft J z hz) *
        hermitianTorusSU J hJ (Units.mk0 z.1.2 hz) * hermitianWeylSU J hJ *
          hermitianUnipotentSU J hJ (hermitianBruhatRight J z hz) := by
  have hconjz : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hz
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change
    ((hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) F) *
        hermitianUnipotentMatrix J z *
        (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) F)) i j =
      (hermitianUnipotentMatrix J (hermitianBruhatLeft J z hz) *
        hermitianTorusMatrix J (Units.mk0 z.1.2 hz) *
        (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) F) *
        hermitianUnipotentMatrix J (hermitianBruhatRight J z hz)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylMatrix, hermitianUnipotentMatrix,
      hermitianTorusMatrix, hermitianBruhatLeft, hermitianBruhatRight,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [hz, hconjz]
  all_goals try rw [J.conj_involutive]
  all_goals try linear_combination z.1.2 * z.2
  all_goals try (ring_nf; done)
  simpa [add_comm, add_left_comm, add_assoc] using z.2.symm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem sum_eq_zero {G : Type*} [Group G] (τ : Representation K G V)
    (C : Subgroup G) [Fintype C] (hz : invariants (τ.comp C.subtype) = ⊥) :
    ∑ c : C, τ c = 0 := by
  ext v
  have hm : (∑ c : C, τ c v) ∈ invariants (τ.comp C.subtype) := by
    rw [mem_invariants]
    intro a
    change τ (a : G) (∑ c : C, τ c v) = _
    simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
    exact Function.Bijective.sum_comp (Group.mulLeft_bijective a) (fun c : C => τ c v)
  simpa [hz] using hm


private theorem root_center_invariants
    (τ : Representation K J.specialSubgroup V)
    (hz : invariants (τ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) = ⊥) :
    invariants ((τ.comp (hermitianUnipotentSU J hJ)).comp
      (center (hermitianUnipotentCoord J)).subtype) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have hm : v ∈ invariants (τ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) := by
    rw [mem_invariants]
    rintro ⟨g, hg⟩
    obtain ⟨r, hr, rfl⟩ := hg
    obtain ⟨c, hc⟩ := (centerCongr (rootEquiv J hJ)).surjective ⟨r, hr⟩
    have he : hermitianUnipotentSU J hJ c.val = (r : J.specialSubgroup) :=
      congrArg (fun t : center (specialRoot J hJ) => (t.val : J.specialSubgroup)) hc
    change τ (r : J.specialSubgroup) v = v
    rw [← he]
    exact hv c
  simpa only [hz, Submodule.mem_bot] using hm

/-- The nonidentity Bruhat summand, linear in the unknown Weyl operator. -/
noncomputable def bruhatTerm (τ : Representation K J.specialSubgroup V)
    (X : Module.End K V) (z : hermitianUnipotentCoord J) : Module.End K V :=
  if hz : z.val.2 = 0 then 0 else
    τ (hermitianUnipotentSU J hJ (hermitianBruhatLeft J z hz) *
      hermitianTorusSU J hJ (Units.mk0 z.val.2 hz)) * X *
    τ (hermitianUnipotentSU J hJ (hermitianBruhatRight J z hz))

/-- Sum the Bruhat summands over each literal coset of the root center. -/
noncomputable def rootCosetOperator [Finite F]
    (τ : Representation K J.specialSubgroup V) (X : Module.End K V) :
    hermitianUnipotentCoord J → Module.End K V := by
  let := Fintype.ofFinite (center (hermitianUnipotentCoord J))
  exact fun z => ∑ c : center (hermitianUnipotentCoord J), bruhatTerm J hJ τ X (z * c.val)

private theorem bruhatTerm_weyl (τ : Representation K J.specialSubgroup V)
    (z : hermitianUnipotentCoord J) :
    bruhatTerm J hJ τ (τ (hermitianWeylSU J hJ)) z =
      τ (hermitianWeylSU J hJ) * τ (hermitianUnipotentSU J hJ z) *
        τ (hermitianWeylSU J hJ) -
      if z.val.2 = 0 then 1 else 0 := by
  classical
  unfold bruhatTerm
  split_ifs with hz
  · rw [coord_eq_one J z hz]
    simp only [map_one, mul_one]
    rw [← map_mul, weyl_square J hJ, map_one, sub_self]
  · simp only [sub_zero, ← map_mul]
    exact congrArg τ (special_weyl_mul_root_mul_weyl J hJ z hz).symm

/-- Zero root-center invariants determine the value of the averaged operator
on the actual Weyl action. The right side is independent of the representation. -/
theorem rootCosetOperator_weyl [Finite F]
    (τ : Representation K J.specialSubgroup V)
    (hz : invariants (τ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) = ⊥)
    (z : hermitianUnipotentCoord J) :
    rootCosetOperator J hJ τ (τ (hermitianWeylSU J hJ)) z =
      -(@Finset.sum (center (hermitianUnipotentCoord J)) (Module.End K V) _
        (@Finset.univ _ (Fintype.ofFinite _))
        (fun c => if (z * c.val).val.2 = 0 then 1 else 0)) := by
  classical
  let := Fintype.ofFinite (center (hermitianUnipotentCoord J))
  have hc := sum_eq_zero (τ.comp (hermitianUnipotentSU J hJ))
    (center (hermitianUnipotentCoord J)) (root_center_invariants J hJ τ hz)
  change (∑ c : center (hermitianUnipotentCoord J),
    τ (hermitianUnipotentSU J hJ c.val)) = 0 at hc
  simp only [rootCosetOperator, bruhatTerm_weyl, Finset.sum_sub_distrib,
    map_mul, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc, hc, zero_mul, mul_zero,
    zero_sub]

/-- The averaged operator depends only on the Borel restriction. -/
theorem rootCosetOperator_eq [Finite F]
    (ρ σ : Representation K J.specialSubgroup V)
    (hb : ∀ g ∈ specialBorel J hJ, ρ g = σ g) :
    rootCosetOperator J hJ ρ = rootCosetOperator J hJ σ := by
  classical
  funext X z
  apply Finset.sum_congr rfl
  intro c _
  unfold bruhatTerm
  split_ifs with h
  · rfl
  · rw [hb _ (mul_mem (mem_sup_left ⟨_, rfl⟩)
      (mem_sup_right ⟨_, rfl⟩)),
      hb _ (mem_sup_left ⟨_, rfl⟩)]

/-- Injectivity of the averaged operator identifies the two Weyl actions. -/
theorem weyl_eq_of_injective [Finite F]
    (ρ σ : Representation K J.specialSubgroup V)
    (hρ : invariants (ρ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) = ⊥)
    (hσ : invariants (σ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) = ⊥)
    (hb : ∀ g ∈ specialBorel J hJ, ρ g = σ g)
    (hinj : Function.Injective (rootCosetOperator J hJ ρ)) :
    ρ (hermitianWeylSU J hJ) = σ (hermitianWeylSU J hJ) := by
  apply hinj
  funext z
  rw [rootCosetOperator_weyl J hJ ρ hρ, rootCosetOperator_eq J hJ ρ σ hb,
    rootCosetOperator_weyl J hJ σ hσ]

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity
