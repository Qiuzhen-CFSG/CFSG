module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.StandardRoots.Coordinates
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.StandardRoots.FixedCoordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Standard root-generated PSL₂ subgroups of SU₃ and PSU₃

The central fixed-field roots and the standard Weyl involution generate the
whole graph-fixed subgroup: under its explicit corner-block equivalence,
these elements supply both SL₂ transvection families. The actual projection
SU₃ → PSU₃ carries this subgroup isomorphically to the projective graph-fixed
subgroup. Finite-field uniqueness then identifies both with the requested
`PSL2BinaryMatrixGroup n`.

The literal commutator torus is the fixed-field diagonal torus. Its action
is transitive on nonzero central roots, and its elements are root–Weyl words.
Thus any nonidentity root involution, the Weyl element and this commutator
torus generate exactly `rootGenerated`, in each original carrier.

Source: GLS4, Chapter 4, Lemma 3.2(d),(h), used in Chapter 2, 16.2 and
16.4–16.5. Arbitrary-pair conjugation belongs to the TwoPointRoots assembly.
The field transport reuses the existing licensed ATLAS `fieldEquivPSL` API.
-/

open Matrix Subgroup BenderSuzuki.External
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.ZD.RankOneModelGeometry.UnitaryStandardRoots
open HermitianForm HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

section CharTwo
variable [CharP E 2]

/-- The actual SU₃ root-generated subgroup is the graph-fixed subgroup. -/
public theorem special_generated_eq_fixed :
    rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) =
      (specialGraphAut J hJ).fixedSubgroup := by
  let H := rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ)
  have hU (b) : specialCentral J hJ b ∈ H := by
    apply Subgroup.mem_sup_left
    rw [special_omega]
    exact ⟨b, rfl⟩
  have hW : hermitianWeylSU J hJ ∈ H := Subgroup.mem_sup_right (mem_zpowers _)
  apply le_antisymm
  · apply sup_le
    · rw [special_omega]
      rintro _ ⟨b, rfl⟩
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      apply Units.ext
      rw [specialGraphAut_apply_val, central_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fixedField_mem]
    · apply zpowers_le.mpr
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      apply Units.ext
      rw [specialGraphAut_apply_val]
      change hermitianWeylMatrix.map J.conj = hermitianWeylMatrix
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hermitianWeylMatrix]
  · have hall (A : SpecialLinearGroup (Fin 2) (fixedField J)) :
        ((specialGraphFixedEquivSL2 J hJ).symm A).val ∈ H := by
      apply Matrix.SL2.transvection_induction (fun A =>
        ((specialGraphFixedEquivSL2 J hJ).symm A).val ∈ H) ?_ ?_ A
      · intro i j hij b
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · have he : ((specialGraphFixedEquivSL2 J hJ).symm
              (SpecialLinearGroup.transvection hij b)).val = specialCentral J hJ (.ofAdd b) := by
            apply Subtype.ext
            apply Units.ext
            rw [fixedEquiv_symm_val, central_val]
            ext i j
            fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]
          rw [he]
          exact hU _
        · have he : ((specialGraphFixedEquivSL2 J hJ).symm
              (SpecialLinearGroup.transvection hij b)).val =
                hermitianWeylSU J hJ * specialCentral J hJ (.ofAdd b) * hermitianWeylSU J hJ := by
            apply Subtype.ext
            apply Units.ext
            simp only [Subgroup.coe_mul, Units.val_mul]
            rw [fixedEquiv_symm_val, central_val]
            change _ = hermitianWeylMatrix * !![1,0,(b:E);0,1,0;0,0,1] * hermitianWeylMatrix
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [SpecialLinearGroup.transvection_coe, hermitianWeylMatrix,
                Matrix.mul_apply, Fin.sum_univ_three]
          rw [he]
          exact H.mul_mem (H.mul_mem hW (hU _)) hW
        · exact (hij rfl).elim
      · intro A B hA hB
        simpa only [map_mul, Subgroup.coe_mul] using H.mul_mem hA hB
    intro x hx
    have hh := hall (specialGraphFixedEquivSL2 J hJ ⟨x, hx⟩)
    simpa only [MulEquiv.symm_apply_apply] using hh

/-- Projecting the SU₃ calculation identifies the actual PSU₃ subgroup. -/
public theorem projective_generated_eq_fixed :
    rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ) =
      (projectiveGraphAut J hJ).fixedSubgroup := by
  rw [← projection_rootGenerated, special_generated_eq_fixed]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [projectiveGraphAut_specialToProjective, (MulAut.mem_fixedSubgroup _ _).mp hx]
  · intro x hx
    obtain ⟨y, hy⟩ := projectiveGraphAut_fixed_representative J hJ ⟨x, hx⟩
    exact ⟨y.val, y.property, hy⟩

theorem special_generation_of_charTwo [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (z : J.specialSubgroup) (hz : z ∈ specialRoot J hJ) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    zpowers z ⊔ zpowers (hermitianWeylSU J hJ) ⊔
      ⁅specialTorus J hJ, zpowers (hermitianWeylSU J hJ)⁆ =
        rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) := by
  rw [special_commutator J hJ hcard hfixed]
  have hzΩ : z ∈ omegaOneAmbient (specialRoot J hJ) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl z hz hz2
  apply le_antisymm
  · exact sup_le (sup_le (zpowers_le.mpr (Subgroup.mem_sup_left hzΩ)) le_sup_right)
      (fixedTorus_le_generated J hJ)
  · let H := zpowers z ⊔ zpowers (hermitianWeylSU J hJ) ⊔ (fixedTorus J hJ).range
    have hΩ : omegaOneAmbient (specialRoot J hJ) ≤ H := by
      rw [special_omega] at hzΩ ⊢
      obtain ⟨b, rfl⟩ := hzΩ
      have hb : b.toAdd ≠ 0 := by
        intro h
        have hb1 : b = 1 := Multiplicative.toAdd.injective h
        exact hz1 (by rw [hb1, map_one])
      rintro _ ⟨c, rfl⟩
      by_cases hc : c.toAdd = 0
      · have hc1 : c = 1 := Multiplicative.toAdd.injective hc
        rw [hc1, map_one]
        exact H.one_mem
      · obtain ⟨a, ha⟩ := fixedTorus_transitive J hJ b.toAdd c.toAdd hb hc
        change fixedTorus J hJ a * specialCentral J hJ b * (fixedTorus J hJ a)⁻¹ =
          specialCentral J hJ c at ha
        rw [← ha]
        have hT : fixedTorus J hJ a ∈ H := Subgroup.mem_sup_right ⟨a, rfl⟩
        have hU : specialCentral J hJ b ∈ H :=
          Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers _))
        exact H.mul_mem (H.mul_mem hT hU) (H.inv_mem hT)
    exact sup_le hΩ (le_trans le_sup_right le_sup_left)


theorem projective_generation_of_charTwo [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ projectiveRoot J hJ)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    zpowers z ⊔ zpowers (hermitianWeylPSU J hJ) ⊔
      ⁅projectiveTorus J hJ, zpowers (hermitianWeylPSU J hJ)⁆ =
        rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ) := by
  obtain ⟨x, rfl⟩ := hz
  have hx2 : x ^ 2 = 1 := EvenInner.root_injective J hJ
    (by simpa only [map_pow, map_one] using hz2)
  have hx1 : hermitianUnipotentSU J hJ x ≠ 1 := by
    intro h
    apply hz1
    rw [← projection_root, h, map_one]
  have hs := special_generation_of_charTwo J hJ hcard hfixed
    (hermitianUnipotentSU J hJ x) ⟨x, rfl⟩ hx1 (by rw [← map_pow, hx2, map_one])
  have hm := congrArg (fun H : Subgroup J.specialSubgroup => H.map J.specialToProjective) hs
  simpa only [Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_zpowers,
    projection_root, projection_weyl, projection_torus, projection_rootGenerated] using hm

noncomputable def fixedFieldEquivBinary [Finite E] {n : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    fixedField J ≃+* BenderSuzuki.PFAppendixIII.BinaryGaloisField n := by
  letI := ZMod.algebra (fixedField J) 2
  exact (GaloisField.algEquivGaloisField 2 n (show Nat.card (fixedField J) = 2 ^ n from hfixed)).toRingEquiv

noncomputable def specialEquiv_of_charTwo [Finite E] {n : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) ≃* PSL2BinaryMatrixGroup n :=
  (MulEquiv.subgroupCongr (special_generated_eq_fixed J hJ)).trans
    ((projectiveGraphFixedEquivSpecial J hJ).symm.trans
      ((projectiveGraphFixedEquiv J hJ).trans
        (Atlas.fieldEquivPSL 2 (fixedFieldEquivBinary J hfixed))))

noncomputable def projectiveEquiv_of_charTwo [Finite E] {n : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ) ≃* PSL2BinaryMatrixGroup n :=
  (MulEquiv.subgroupCongr (projective_generated_eq_fixed J hJ)).trans
    ((projectiveGraphFixedEquiv J hJ).trans
      (Atlas.fieldEquivPSL 2 (fixedFieldEquivBinary J hfixed)))

end CharTwo

variable [Finite E]

private theorem binary_charTwo {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2) : CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

/-- The standard SU₃ root-generated subgroup is PSL₂ over the binary field.
This equivalence is on the actual special-unitary carrier, without quotienting
its center in advance. -/
public noncomputable def specialEquivPSL2 {n : ℕ} (_hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) ≃* PSL2BinaryMatrixGroup n := by
  let : CharP E 2 := binary_charTwo hcard
  exact specialEquiv_of_charTwo J hJ hfixed

/-- The standard PSU₃ root-generated subgroup is PSL₂ over the binary field. -/
public noncomputable def projectiveEquivPSL2 {n : ℕ} (_hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ) ≃* PSL2BinaryMatrixGroup n := by
  let : CharP E 2 := binary_charTwo hcard
  exact projectiveEquiv_of_charTwo J hJ hfixed

/-- Every nonidentity involution of the standard special root group supplies
all of its omega subgroup after adjoining the Weyl commutator torus. -/
public theorem special_generation {n : ℕ} (_hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (z : J.specialSubgroup) (hz : z ∈ specialRoot J hJ) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    zpowers z ⊔ zpowers (hermitianWeylSU J hJ) ⊔
      ⁅specialTorus J hJ, zpowers (hermitianWeylSU J hJ)⁆ =
        rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) := by
  let : CharP E 2 := binary_charTwo hcard
  exact special_generation_of_charTwo J hJ hcard hfixed z hz hz1 hz2

/-- The same single-involution generation identity in the actual projective image. -/
public theorem projective_generation {n : ℕ} (_hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ projectiveRoot J hJ)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    zpowers z ⊔ zpowers (hermitianWeylPSU J hJ) ⊔
      ⁅projectiveTorus J hJ, zpowers (hermitianWeylPSU J hJ)⁆ =
        rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ) := by
  let : CharP E 2 := binary_charTwo hcard
  exact projective_generation_of_charTwo J hJ hcard hfixed z hz hz1 hz2

end BenderSuzuki.ZD.RankOneModelGeometry.UnitaryStandardRoots
