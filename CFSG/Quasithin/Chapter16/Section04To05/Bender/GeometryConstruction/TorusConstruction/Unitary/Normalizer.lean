module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Unitary.SplitTorus

/-!
# The normalizer action on the unitary omega layer

The nontrivial central layer has a unique fixed point on the isotropic points:
the root group acts regularly away from its fixed point. Therefore a normalizer
of the central layer lies in that point's Borel stabilizer. Root elements act
trivially on the layer; a full diagonal torus element acts by its inverse norm.
Every such scalar is an inverse square of a fixed-field unit. This proves
pointwise coverage by the split torus, for the literal conjugation action.

Source: Aschbacher–Smith, Proposition 16.5.1, printed p.1194, third paragraph;
the isotropic-point action and its Borel are Huppert II.10.12.
-/

public section

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Unitary
open BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) := Quotient.finite _
variable (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem normalizer_le_point_stabilizer {H A : Type*} [Group H] [MulAction H A]
    (R Z : Subgroup H) (a : A) (hZR : Z ≤ R)
    (hRa : R ≤ MulAction.stabilizer H a) (hZ : Z ≠ ⊥)
    (hregular : ∀ b c : A, b ≠ a → c ≠ a → ∃! r : R, (r : H) • b = c) :
    normalizer (Z : Set H) ≤ MulAction.stabilizer H a := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  by_contra hga
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hZ
  have hgz : g⁻¹ * (z : H) * g ∈ Z := by
    have h := mem_normalizer_iff.mp hg (g⁻¹ * (z : H) * g)
    apply h.mpr
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using z.property
  have hzfix : (z : H) • (g • a) = g • a := by
    calc
      _ = g • ((g⁻¹ * (z : H) * g) • a) := by simp [mul_smul]
      _ = _ := by rw [MulAction.mem_stabilizer_iff.mp (hRa (hZR hgz))]
  have hreg := hregular (g • a) (g • a) hga hga
  have he : (⟨z, hZR z.property⟩ : R) = 1 := hreg.unique hzfix (by simp)
  exact hz (Subtype.ext (congrArg (fun r : R => (r : H)) he))

/-- The omega normalizer is contained in the genuine matrix Borel. -/
theorem central_normalizer_le_borel {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    normalizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      BorelTorus.projectiveBorel J hJ := by
  classical
  obtain ⟨_, rho, pinf, _, _, _, hr, _⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, D, hRU, _, _, _, hsup, _, _, _, _, _, hregular, ⟨coord, hcoord⟩, hDcoord, hDsurj⟩ := hr
  have hroot (z : hermitianUnipotentCoord J) :
      (coord z : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    apply Subtype.ext
    rw [hproj, hermitianUnipotentPSU_val]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun hM i) j
  have hR : R = BorelTorus.projectiveRoot J hJ := by
    ext g
    constructor
    · intro hg
      obtain ⟨z, hz⟩ := coord.surjective ⟨g, hg⟩
      exact ⟨z, (hroot z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro ⟨z, rfl⟩
      rw [← hroot]
      exact (coord z).property
  have hD : D = BorelTorus.projectiveTorus J hJ := by
    ext g
    constructor
    · intro hg
      obtain ⟨k, M, hM, hproj⟩ := hDcoord ⟨g, hg⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      rw [hproj, hermitianTorusPSU_val]
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact (congrFun (congrFun hM i) j).symm
    · rintro ⟨k, rfl⟩
      obtain ⟨h, M, hM, hproj⟩ := hDsurj k
      have he : (h : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        rw [hproj, hermitianTorusPSU_val]
        congr 1
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        exact congrFun (congrFun hM i) j
      rw [← he]
      exact h.property
  let P := Projectivization E (Fin 3 → E)
  let A : Set P := {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
    x = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) Omega := MulAction.compHom Omega rho
  have hZ : centralImage J hJ ≠ ⊥ := by
    intro he
    have hb : centralMap J hJ (Multiplicative.ofAdd 1) = 1 :=
      mem_bot.mp (he ▸ (show centralMap J hJ (Multiplicative.ofAdd 1) ∈ centralImage J hJ from ⟨_, rfl⟩))
    have hh : (Multiplicative.ofAdd 1 : Multiplicative (fixedField J)) = 1 :=
      centralMap_injective J hJ (hb.trans (map_one _).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd hh)
  have hzR : centralImage J hJ ≤ R := by rw [hR]; exact centralImage_le_root J hJ
  have hh := normalizer_le_point_stabilizer R (centralImage J hJ) pinf hzR hRU hZ hregular
  change normalizer _ ≤ _ at hh
  rw [BorelTorus.projectiveBorel, ← hR, ← hD, hsup]
  exact hh

/-- A full diagonal actor has exactly the same omega action as a split actor. -/
theorem full_torus_coverage (k : Eˣ) :
    ∃ x : splitImage J hJ, ∀ u ∈ centralImage J hJ,
      MulAut.conj (x : ProjectiveSpecialUnitaryMatrixGroup J) u =
        MulAut.conj (hermitianTorusPSU J hJ k) u := by
  let t : fixedField J := ⟨J.conj (k : E) * (k : E), by
    change J.conj (J.conj (k : E) * (k : E)) = _
    rw [map_mul, J.conj_involutive, mul_comm]⟩
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective
    (CharTwo.sq_injective : Function.Injective (fun x : fixedField J => x ^ 2)) t
  change a ^ 2 = t at ha
  have ha0 : a ≠ 0 := by
    intro he
    have hh := congrArg (fun b : fixedField J => (b : E)) ha
    have hh' : J.conj (k : E) * (k : E) = 0 := by
      simpa only [he, zero_pow (by decide : 2 ≠ 0), Subfield.coe_zero] using hh.symm
    exact (mul_ne_zero ((map_ne_zero J.conj).mpr (Units.ne_zero k)) (Units.ne_zero k)) hh'
  refine ⟨⟨splitMap J hJ (Units.mk0 a ha0), ⟨_, rfl⟩⟩, ?_⟩
  rintro _ ⟨b, rfl⟩
  change MulAut.conj (splitMap J hJ (Units.mk0 a ha0)) (centralMap J hJ b) = _
  rw [split_action]
  change hermitianUnipotentPSU J hJ (centralCoord J _) =
    hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ (centralCoord J b) *
      (hermitianTorusPSU J hJ k)⁻¹
  rw [EvenInner.projective_torus_action]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · simp only [hermitianTorusAction_fst]
    change 0 = 0 * _ * _
    simp
  · rw [hermitianTorusAction_snd]
    change (b.toAdd * a⁻¹ ^ 2 : fixedField J).val =
      (b.toAdd : E) * (J.conj (k : E))⁻¹ * (k : E)⁻¹
    have he : (a : E) ^ 2 = J.conj (k : E) * (k : E) :=
      congrArg (fun c : fixedField J => (c : E)) ha
    simp only [Subfield.coe_mul, SubmonoidClass.coe_pow, Subfield.coe_inv, inv_pow, he, mul_inv_rev]
    ring

/-- The split torus covers the entire omega normalizer action pointwise. -/
theorem normalizer_coverage {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ normalizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    ∃ x : splitImage J hJ, ∀ u ∈ centralImage J hJ,
      MulAut.conj (x : ProjectiveSpecialUnitaryMatrixGroup J) u = MulAut.conj g u := by
  have hnorm : BorelTorus.projectiveTorus J hJ ≤
      normalizer (BorelTorus.projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rintro _ ⟨k, rfl⟩
    apply mem_normalizer_fintype
    rintro _ ⟨z, rfl⟩
    rw [EvenInner.projective_torus_action]
    exact ⟨_, rfl⟩
  have hgB := central_normalizer_le_borel J hJ hcard hfixed hg
  have hgprod : g ∈ (BorelTorus.projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) *
      (BorelTorus.projectiveTorus J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hgB
  obtain ⟨r, hr, d, ⟨k, rfl⟩, rfl⟩ := hgprod
  obtain ⟨x, hx⟩ := full_torus_coverage J hJ k
  refine ⟨x, ?_⟩
  intro u hu
  rw [hx u hu]
  have hdu : MulAut.conj (hermitianTorusPSU J hJ k) u ∈ centralImage J hJ := by
    rw [← hx u hu]
    exact (mem_normalizer_iff.mp (split_normalizes_central J hJ x.property) u).mp hu
  have hc := mem_centralizer_iff.mp (root_centralizes J hJ hr) _ hdu
  change _ = (r * hermitianTorusPSU J hJ k) * u * (r * hermitianTorusPSU J hJ k)⁻¹
  calc
    _ = r * MulAut.conj (hermitianTorusPSU J hJ k) u * r⁻¹ := by
      rw [← hc, mul_inv_cancel_right]
    _ = _ := by simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Unitary
