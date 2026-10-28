module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Coordinates
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.TorusWeights

/-!
# Recovering the field automorphism from the projective torus action

Restrict an ambient automorphism to the root coordinates and pass to the
additive first-coordinate equivalence. Normalize its value at one by a scalar.
Torus preservation intertwines every torus weight with another weight, without
choosing an automorphism of the covering unit group. Since these weights span
the field additively, the normalized map is multiplicative and is a field
automorphism.

This implements Steinberg, Theorem 36, steps (3)–(4), in
`refs/KGroup/GLS3/Chapter2St1.tex`, including the projective scalar ambiguity
and fixed-field prime three. Torus preservation itself, and compatibility
with the opposite root, are separate inputs to the final rigidity theorem.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

public theorem first_field_of_torus_intertwining [Finite E] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hcard : Nat.card E = p ^ 2) (h2 : (2 : E) ≠ 0)
    (φ : MulAut (hermitianUnipotentCoord J))
    (hact : ∀ k : Eˣ, ∃ l : Eˣ, ∀ z : hermitianUnipotentCoord J,
      φ (hermitianTorusAction J k z) = hermitianTorusAction J l (φ z)) :
    ∃ (σ : E ≃+* E) (t : Eˣ), ∀ z : hermitianUnipotentCoord J,
      (φ z).val.1 = (t : E) * σ z.val.1 := by
  let f₀ := coordFirstAddEquiv J h2 φ
  have hnz : f₀ 1 ≠ 0 := by simp
  let t : Eˣ := Units.mk0 (f₀ 1) hnz
  let f : E ≃+ E :=
    { toFun := fun a => (t : E)⁻¹ * f₀ a
      invFun := fun a => f₀.symm ((t : E) * a)
      left_inv := fun a => by simp
      right_inv := fun a => by simp
      map_add' := fun a b => by simp only [map_add, mul_add] }
  have hweight (k : Eˣ) : ∃ l : Eˣ, ∀ a : E,
      f₀ ((torusWeight J k : E) * a) = (torusWeight J l : E) * f₀ a := by
    obtain ⟨l, hl⟩ := hact k
    refine ⟨l, fun a => ?_⟩
    obtain ⟨z, rfl⟩ := coord_first_surjective J h2 a
    have he := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) (hl z)
    rw [← coordFirstAddEquiv_apply J h2 φ, hermitianTorusAction_fst, hermitianTorusAction_fst,
      ← coordFirstAddEquiv_apply J h2 φ] at he
    simpa [f₀, torusWeight_val, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using he
  have hfweight (k : Eˣ) (a : E) : f ((torusWeight J k : E) * a) =
      f (torusWeight J k : E) * f a := by
    obtain ⟨l, hl⟩ := hweight k
    have hl1 := hl 1
    rw [mul_one] at hl1
    change (t : E)⁻¹ * f₀ ((torusWeight J k : E) * a) =
      ((t : E)⁻¹ * f₀ (torusWeight J k : E)) * ((t : E)⁻¹ * f₀ a)
    rw [hl a, hl1]
    change _ = ((t : E)⁻¹ * ((torusWeight J l : E) * (t : E))) * _
    field_simp
  let σ : E ≃+* E :=
    { f with map_mul' := mul_eq_of_torusWeight J hp hp3 hcard f hfweight }
  refine ⟨σ, t, fun z => ?_⟩
  change (φ z).val.1 = (t : E) * ((t : E)⁻¹ * f₀ z.val.1)
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero t), one_mul]
  exact (coordFirstAddEquiv_apply J h2 φ z).symm

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

public theorem rootCoordinateAut_torus_intertwining
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hT : (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ) :
    ∀ k : Eˣ, ∃ l : Eˣ, ∀ z : hermitianUnipotentCoord J,
      rootCoordinateAut J hJ b hU (hermitianTorusAction J k z) =
        hermitianTorusAction J l (rootCoordinateAut J hJ b hU z) := by
  intro k
  have hm : b (hermitianTorusPSU J hJ k) ∈ rootTorus J hJ := by
    rw [← hT]
    exact ⟨hermitianTorusPSU J hJ k, ⟨k, rfl⟩, rfl⟩
  obtain ⟨l, hl⟩ := hm
  refine ⟨l, fun z => ?_⟩
  apply root_injective J hJ
  apply mul_right_cancel (b := hermitianTorusPSU J hJ l)
  rw [rootCoordinateAut_spec, ← hermitianTorusPSU_mul_unipotent,
    rootCoordinateAut_spec, hl, ← map_mul]
  simpa only [map_mul] using congrArg b (hermitianTorusPSU_mul_unipotent J hJ k z).symm

public theorem two_ne_zero_of_prime_square [Finite E] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hcard : Nat.card E = p ^ 2) : (2 : E) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite E
  let := charP_of_card_eq_prime_pow (by simpa using hcard : Fintype.card E = p ^ 2)
  intro h2
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff E p 2).mp (by simpa using h2)
  have hh := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

public theorem root_first_field_of_torus_preserving [Finite E] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hcard : Nat.card E = p ^ 2)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hT : (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ) :
    ∃ (σ : E ≃+* E) (t : Eˣ), ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1 :=
  first_field_of_torus_intertwining J hp hp3 hcard
    (two_ne_zero_of_prime_square hp hp3 hcard) (rootCoordinateAut J hJ b hU)
    (rootCoordinateAut_torus_intertwining J hJ b hU hT)

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
