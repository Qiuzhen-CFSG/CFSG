module
public import Theory.GroupAction.CartanPanelFixedPoints.Regular
public import Theory.SpecificGroups.SU3.BorelTorus.EvenCenterAction
public import BenderSuzuki.SE.Borel

/-!
# Sharp Cartan elements in the binary unitary Borel

A nonidentity fixed-field unit scales the two root coordinates by k⁻¹ and
k⁻². In characteristic two both displacements are invertible. Huppert's
regular action on the punctured isotropic point set therefore gives exactly
two fixed points. The commutator bijection places a conjugate in every
supplied root supplement; the orbit map gives the literal normalizer-coset
assertion. The projective scalar kernel is retained throughout.

Source: Huppert, Endliche Gruppen I, II.10.12, pp.264--265.
-/

public section
open BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.CartanPanel
open BorelTorus.EvenCenterAction
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- A fixed field of order greater than two supplies a nonidentity unit. -/
theorem exists_fixed_unit [Finite F] {q : ℕ}
    (hfixed : Nat.card {x : F // J.conj x = x} = q) (hq : 2 < q) :
    ∃ k : Fˣ, (k : F) ≠ 1 ∧ J.conj (k : F) = k := by
  have hc : 1 < Nat.card (fixedField J)ˣ := by
    rw [Nat.card_units]
    change 1 < Nat.card {x : F // J.conj x = x} - 1
    omega
  let : Nontrivial (fixedField J)ˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨k, hk⟩ := exists_ne (1 : (fixedField J)ˣ)
  refine ⟨Units.map (fixedField J).subtype.toMonoidHom k, ?_, k.val.property⟩
  intro he
  exact hk (Units.ext (Subtype.ext he))

/-- A nonidentity fixed-field unit has trivial centralizer on the root coordinates. -/
theorem fixed_unit_root_free [CharP F 2] (k : Fˣ)
    (hk : (k : F) ≠ 1) (hfixed : J.conj (k : F) = k)
    (z : hermitianUnipotentCoord J) (he : hermitianTorusAction J k z = z) : z = 1 := by
  have hk2 : (k : F)^2 ≠ 1 := by
    intro h
    exact hk (CharTwo.sq_injective (h.trans (one_pow 2).symm))
  have hw1 : (k : F) * (k : F)⁻¹ ^ 2 ≠ 1 := by
    have heq : (k : F) * (k : F)⁻¹ ^ 2 = (k : F)⁻¹ := by field_simp
    rw [heq]
    exact inv_ne_one.mpr hk
  have hw2 : (k : F)⁻¹ * (k : F)⁻¹ ≠ 1 := by
    rw [← pow_two, inv_pow]
    exact inv_ne_one.mpr hk2
  have h1 := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) he
  have h2 := congrArg (fun z : hermitianUnipotentCoord J => z.val.2) he
  rw [hermitianTorusAction_fst, hfixed] at h1
  rw [hermitianTorusAction_snd, hfixed] at h2
  have hz1 : z.val.1 = 0 := by
    have hh : z.val.1 * ((k : F) * (k : F)⁻¹ ^ 2 - 1) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hw1)
  have hz2 : z.val.2 = 0 := by
    have hh : z.val.2 * ((k : F)⁻¹ * (k : F)⁻¹ - 1) = 0 := by linear_combination h2
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hw2)
  exact Subtype.ext (Prod.ext hz1 hz2)

variable [Finite F] [CharP F 2]
open Theory.CartanPanel BenderSuzuki
open scoped LinearAlgebra.Projectivization

/-- In the actual projective unitary group, every supplement to the standard
root group in its normalizer contains an element fixing exactly two cosets.
No injectivity of the projective torus is assumed. -/
theorem projective_root_two_fixed_cosets
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {q : ℕ}
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) (hq : 2 < q)
    (D : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hD : D ≤ Subgroup.normalizer ((hermitianUnipotentPSU J hJ).range : Set _))
    (hsup : (hermitianUnipotentPSU J hJ).range ⊔ D =
      Subgroup.normalizer ((hermitianUnipotentPSU J hJ).range : Set _)) :
    HasTwoFixedCosets
      (Subgroup.normalizer ((hermitianUnipotentPSU J hJ).range : Set _)) D := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨hOmega, rho, α, _hrho, _hnatural, _hBcard,
    ⟨R, H, hR, hH, hBN, _hdis, _hsup, _hcyc, hRcard,
      _hcomm, _hcommcard, _hHcard, hreg, ⟨coord, hcoord⟩, _hHcoord, hHsurj⟩,
    htwo, _hGcard, _hthree⟩ := huppert_II_10_12 J q hcard hfixed hJ
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, heq⟩ := hcoord z
    have hM' : M = hermitianUnipotentGL J z := Units.ext hM
    apply Subtype.ext
    simpa only [hM', hermitianUnipotentPSU_val] using heq
  have hRe : R = (hermitianUnipotentPSU J hJ).range := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨z, (hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z, rfl⟩
      rw [← hcoord_eq z]
      exact (coord z).property
  let P := ℙ F (Fin 3 → F)
  let A : Set P := {x | ∃ (v : Fin 3 → F) (hv : v ≠ 0),
    x = Projectivization.mk F v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) Omega :=
    MulAction.compHom _ rho
  have hRne : R ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hRcard
    have hp : 1 < q ^ 3 := one_lt_pow₀ (by omega) (by decide)
    omega
  have hN : Subgroup.normalizer (R : Set _) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) α :=
    normalizer_eq_stabilizer_of_regular_compl R α hR hRne hreg hBN
  have hOmega' : 1 < Nat.card Omega := by
    rw [hOmega]
    have hp : 0 < q ^ 3 := pow_pos (by omega) _
    omega
  let : Nontrivial Omega := Finite.one_lt_card_iff_nontrivial.mp hOmega'
  obtain ⟨k, hk, hkfix⟩ := exists_fixed_unit J hfixed hq
  let t := hermitianTorusPSU J hJ k
  have htH : t ∈ H := by
    obtain ⟨h, M, hM, heq⟩ := hHsurj k
    have hM' : M = hermitianTorusGL J k := Units.ext hM
    have hh : (h : ProjectiveSpecialUnitaryMatrixGroup J) = t := by
      apply Subtype.ext
      simpa only [t, hM', hermitianTorusPSU_val] using heq
    exact hh ▸ h.property
  have ht : t ∈ Subgroup.normalizer (R : Set _) := hBN (hH htH)
  have hta : t • α = α := hH htH
  have hfree : ∀ r : R, t * r * t⁻¹ = r → r = 1 := by
    intro r hr
    have hrange : (r : ProjectiveSpecialUnitaryMatrixGroup J) ∈
        (hermitianUnipotentPSU J hJ).range := by rw [← hRe]; exact r.property
    obtain ⟨z, hz⟩ := hrange
    have he : hermitianTorusAction J k z = z := by
      apply EvenInner.root_injective J hJ
      rw [← EvenInner.projective_torus_action, hz]
      exact hr
    have hz1 := fixed_unit_root_free J k hk hkfix z he
    apply Subtype.ext
    rw [← hz, hz1, map_one]
    rfl
  obtain ⟨β, hβ, hfix⟩ := two_fixed_of_regular R α hR hreg (exists_ne α) t ht hta hfree
  rw [← hRe] at hD hsup ⊢
  apply two_fixed_cosets _ D α hN
  · intro x
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨g, hg, _⟩ := htwo α β x y hβ.symm hy.symm
    exact ⟨g, hg⟩
  · exact two_fixed_in_supplement R D α β hβ hR hD t ht
      (hsup.symm ▸ ht) hfree hfix

end BenderSuzuki.MatrixGroups.HermitianForm.CartanPanel
