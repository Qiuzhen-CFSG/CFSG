module

public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.SpecificGroups.SU3.OrthogonalFixed
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.OrthogonalOrder
public import Theory.GroupTheory.TwoCosetExtension
public import Mathlib.GroupTheory.Sylow
import all Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison

/-!
# Fixed cyclic two-groups in the split Hermitian torus

Work in the entrywise fixed subgroup of the special unitary group. Its
orthogonal model gives order p(p²-1). The literal diagonal torus and its
Weyl coset form a subgroup of order 2(p-1), whose index is odd for p ≡ 1
modulo four. Sylow conjugacy puts a two-subgroup in this extension. Every
element outside the torus squares to one, so a generator of order greater
than two lies in the torus. The injective fixed-point projectivization
returns the original projective conjugator and diagonal parameter.

The internal `GraphComparison` import identifies its fixed-point projection
with the original `specialToProjective` map. This is an intentional
continuation of that construction, without changing its public boundary.
Source: Aschbacher--Smith E.1.14(7), printed p.214, and Aschbacher (1982),
Lemma 4.11; the explicit matrices are those of Huppert II.10.12.
-/

open Matrix Subgroup BenderSuzuki.External
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.FixedCyclicTorusPlacement
open OddPrimeSylow
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
variable {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} (hγ : J.IsEntrywiseConjugation γ)

private theorem conjugate_into {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (hi : ¬ 2 ∣ D.index) (x : G) (hx : IsPGroup 2 (zpowers x)) :
    ∃ g : G, MulAut.conj g x ∈ D := by
  let Q : Sylow 2 D := Sylow.nonempty.some
  have hQ : ¬ 2 ∣ (Q.map D.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two Q.not_dvd_index hi
  let R : Sylow 2 G := (Q.isPGroup'.map D.subtype).toSylow hQ
  obtain ⟨P, hP⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
  have hm : MulAut.conj g x ∈ (R : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP (mem_zpowers x))
  exact ⟨g, Subgroup.map_subtype_le (Q : Subgroup D) hm⟩

private theorem card_two_coset {G : Type*} [Group G] (K : Subgroup G) [Finite K] (a : G)
    (hs : a * a ∈ K) (hc : ∀ k ∈ K, a⁻¹ * k * a ∈ K) (ha : a ∉ K) :
    Nat.card (twoCosetExtension K a hs hc) = 2 * Nat.card K := by
  have hinj : Function.Injective (twoCosetExtensionCover K a hs hc) := by
    rintro ⟨b, k⟩ ⟨c, l⟩ h
    have he := congrArg Subtype.val h
    cases b <;> cases c
    · have : k = l := Subtype.ext he
      exact congrArg (Prod.mk false) this
    · change (k : G) = a * (l : G) at he
      exact (ha (by
        rw [eq_mul_inv_iff_mul_eq.mpr he.symm]
        exact K.mul_mem k.property (K.inv_mem l.property))).elim
    · change a * (k : G) = (l : G) at he
      exact (ha (by
        rw [eq_mul_inv_iff_mul_eq.mpr he]
        exact K.mul_mem l.property (K.inv_mem k.property))).elim
    · have : k = l := Subtype.ext (mul_left_cancel he)
      exact congrArg (Prod.mk true) this
  have h := Nat.card_congr (Equiv.ofBijective (twoCosetExtensionCover K a hs hc)
    ⟨hinj, twoCosetExtensionCover_surjective K a hs hc⟩)
  simpa using h.symm

private theorem torus_capture {G A : Type*} [Group G] [Group A] [Finite G]
    (f : A →* G) (a : G) (ha : a * a = 1) (han : a ∉ f.range)
    (haf : ∀ c, a * f c = f c⁻¹ * a)
    {p : ℕ} (hp : 1 < p) (hmod : p % 4 = 1)
    (hG : Nat.card G = p * (p ^ 2 - 1)) (hK : Nat.card f.range = p - 1)
    (x : G) (hx : IsPGroup 2 (zpowers x)) (hlarge : 2 < orderOf x) :
    ∃ g c, MulAut.conj g x = f c := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hc : ∀ k ∈ f.range, a⁻¹ * k * a ∈ f.range := by
    rintro k ⟨c, rfl⟩
    rw [hai, haf, mul_assoc, ha, mul_one]
    exact ⟨c⁻¹, rfl⟩
  let D := twoCosetExtension f.range a (ha ▸ f.range.one_mem) hc
  have hD : Nat.card D = 2 * (p - 1) := (card_two_coset _ _ _ _ han).trans (by rw [hK])
  have hprod := D.card_mul_index
  rw [hD, hG] at hprod
  have hfac : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq p 1
  rw [hfac] at hprod
  have hi : 2 * D.index = p * (p + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < p - 1 by omega)
    nlinarith [hprod]
  have hp2 : p + 1 = 2 * ((p + 1) / 2) := by omega
  have hid : D.index = p * ((p + 1) / 2) := by nlinarith [hi]
  have hodd : Odd D.index := by
    rw [hid]
    apply Odd.mul <;> rw [Nat.odd_iff] <;> omega
  obtain ⟨g, hg⟩ := conjugate_into D
    (by simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hodd) x hx
  change MulAut.conj g x ∈ f.range ∨ ∃ k ∈ f.range, MulAut.conj g x = a * k at hg
  rcases hg with ⟨c, he⟩ | ⟨k, ⟨c, rfl⟩, he⟩
  · exact ⟨g, c, he.symm⟩
  · have hs : (MulAut.conj g x) ^ 2 = 1 := by
      rw [he, pow_two]
      calc
        a * f c * (a * f c) = (f c⁻¹ * a) * (a * f c) :=
          congrArg (fun t => t * (a * f c)) (haf c)
        _ = f c⁻¹ * (a * a) * f c := by group
        _ = 1 := by simp [ha]
    have hx2 : x ^ 2 = 1 := (MulAut.conj g).injective (by simpa using hs)
    have := Nat.le_of_dvd (by decide : 0 < 2) (orderOf_dvd_of_pow_eq_one hx2)
    omega

private def torusSU : (FixedBy.subfield F J.conj)ˣ →* J.specialSubgroup :=
  (hermitianTorusSU J hJ).comp
    (Units.map (FixedBy.subfield F J.conj).subtype.toMonoidHom)

private theorem torusSU_matrix (c : (FixedBy.subfield F J.conj)ˣ) :
    (torusSU J hJ c).val.val =
      !![((c⁻¹ : (FixedBy.subfield F J.conj)ˣ) : F),0,0;0,1,0;0,0,(c : F)] := by
  have hc : J.conj (c : F) = (c : F) := (c : FixedBy.subfield F J.conj).property
  change hermitianTorusMatrix J (Units.map (FixedBy.subfield F J.conj).subtype.toMonoidHom c) = _
  simp [hermitianTorusMatrix, hc, Units.ne_zero c]

private theorem torusSU_fixed (c : (FixedBy.subfield F J.conj)ˣ) :
    specialEntrywiseAut J hγ (torusSU J hJ c) = torusSU J hJ c := by
  apply Subtype.ext
  apply Units.ext
  rw [specialEntrywiseAut_val, torusSU_matrix]
  have hc : J.conj (c : F) = (c : F) := (c : FixedBy.subfield F J.conj).property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, hc]

private def torus : (FixedBy.subfield F J.conj)ˣ →*
    (specialEntrywiseAut J hγ).fixedSubgroup :=
  (torusSU J hJ).codRestrict _ (fun c => (MulAut.mem_fixedSubgroup _ _).mpr
    (torusSU_fixed J hJ hγ c))

private theorem torus_injective : Function.Injective (torus J hJ hγ) := by
  intro c d h
  apply Units.ext
  apply Subtype.ext
  have he := congrArg (fun z : (specialEntrywiseAut J hγ).fixedSubgroup =>
    z.val.val.val 2 2) h
  change (torusSU J hJ c).val.val 2 2 = (torusSU J hJ d).val.val 2 2 at he
  simpa [torusSU_matrix] using he

private def weyl : (specialEntrywiseAut J hγ).fixedSubgroup :=
  ⟨hermitianWeylSU J hJ, by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    apply Units.ext
    rw [specialEntrywiseAut_val]
    change (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) F).map J.conj = hermitianWeylMatrix
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianWeylMatrix, Matrix.map_apply]⟩

private theorem weyl_sq : weyl J hJ hγ * weyl J hJ hγ = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) F) * hermitianWeylMatrix = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weyl_mul_torus (c : (FixedBy.subfield F J.conj)ˣ) :
    weyl J hJ hγ * torus J hJ hγ c = torus J hJ hγ c⁻¹ * weyl J hJ hγ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change hermitianWeylMatrix * (torusSU J hJ c).val.val =
    (torusSU J hJ c⁻¹).val.val * hermitianWeylMatrix
  rw [torusSU_matrix, torusSU_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weyl_not_mem : weyl J hJ hγ ∉ (torus J hJ hγ).range := by
  rintro ⟨c, hc⟩
  have he := congrArg (fun z : (specialEntrywiseAut J hγ).fixedSubgroup =>
    z.val.val.val 0 2) hc
  change (torusSU J hJ c).val.val 0 2 = hermitianWeylMatrix 0 2 at he
  simp [torusSU_matrix, hermitianWeylMatrix] at he


include hγ in
/-- Larger cyclic two-groups fixed by entrywise conjugation are conjugate,
by a fixed projective element, into the literal split Hermitian torus. -/
public theorem exists_fixed_torus_conjugator [Finite F]
    {p : ℕ} (hp : 1 < p) (ho : Odd p) (hmod : p % 4 = 1)
    (hfixed : Nat.card (FixedBy.subfield F J.conj) = p)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : γ x = x)
    (hx2 : IsPGroup 2 (zpowers x)) (hlarge : 2 < orderOf x) :
    ∃ y : ProjectiveSpecialUnitaryMatrixGroup J, γ y = y ∧
      ∃ c : (FixedBy.subfield F J.conj)ˣ,
        MulAut.conj y x = hermitianTorusPSU J hJ
          (Units.map (FixedBy.subfield F J.conj).subtype.toMonoidHom c) := by
  let K := FixedBy.subfield F J.conj
  have h2 : (2 : K) ≠ 0 := by
    apply Ring.two_ne_zero
    intro he
    let := Fintype.ofFinite K
    have hh := FiniteField.even_card_of_char_two he
    rw [← Nat.card_eq_fintype_card, hfixed] at hh
    have := Nat.odd_iff.mp ho
    omega
  let H := (specialEntrywiseAut J hγ).fixedSubgroup
  have hH : Nat.card H = p * (p ^ 2 - 1) := by
    calc
      Nat.card H = Nat.card (splitOrthogonalForm K).specialSubgroup :=
        Nat.card_congr (Equiv.ofBijective (specialFixedToOrthogonal J hJ hγ)
          ⟨specialFixedToOrthogonal_injective J hJ hγ,
            specialFixedToOrthogonal_surjective J hJ hγ⟩)
      _ = p * (p ^ 2 - 1) := by rw [card_splitOrthogonal_specialSubgroup h2, hfixed]
  have hT : Nat.card (torus J hJ hγ).range = p - 1 := by
    calc
      Nat.card (torus J hJ hγ).range = Nat.card Kˣ :=
        Nat.card_range_of_injective (torus_injective J hJ hγ)
      _ = p - 1 := by rw [Nat.card_units, hfixed]
  let f : H →* ProjectiveSpecialUnitaryMatrixGroup J :=
    J.specialToProjective.comp H.subtype
  have hf : Function.Injective f := by
    intro a b he
    exact fixedProjectiveHom_injective J hγ (Subtype.ext he)
  obtain ⟨z, hz⟩ := fixedProjectiveHom_surjective J hγ
    ⟨x, (MulAut.mem_fixedSubgroup _ _).mpr hx⟩
  have hzx : f z = x := congrArg Subtype.val hz
  have hz2 : IsPGroup 2 (zpowers z) := by
    apply (hx2.comap_of_injective f hf).to_le
    apply zpowers_le.mpr
    change f z ∈ zpowers x
    rw [hzx]
    exact mem_zpowers x
  have hzl : 2 < orderOf z := by
    rw [← orderOf_injective f hf z, hzx]
    exact hlarge
  obtain ⟨y, c, hyc⟩ := torus_capture (torus J hJ hγ) (weyl J hJ hγ)
    (weyl_sq J hJ hγ) (weyl_not_mem J hJ hγ) (weyl_mul_torus J hJ hγ)
    hp hmod hH hT z hz2 hzl
  refine ⟨f y, ?_, c, ?_⟩
  · exact (MulAut.mem_fixedSubgroup _ _).mp (fixedProjectiveHom J hγ y).property
  · have he := congrArg f hyc
    change f (y * z * y⁻¹) = f (torus J hJ hγ c) at he
    rw [map_mul, map_mul, map_inv, hzx] at he
    change f y * x * (f y)⁻¹ = _
    rw [he]
    apply Subtype.ext
    change (J.specialToProjective (torusSU J hJ c)).val = _
    rw [specialToProjective_apply_val, hermitianTorusPSU_val]
    rfl

end BenderSuzuki.MatrixGroups.HermitianForm.FixedCyclicTorusPlacement
