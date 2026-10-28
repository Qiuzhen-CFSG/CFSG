module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.Contracts
public import Theory.Combinatorics.ProjectivePlaneMatrixAction

/-!
# Root lines in the marked quotient axis

Root groups defined using the original natural marking correspond exactly to
one-dimensional defining-field spaces of axis shear parameters. Conjugation
preserves the root family, and inverse transpose interchanges its two indices
and negates its parameter. Thus the comparison uses both recorded quotient
orientations and the original marking throughout.

A conjugate elementary root has matrix displacement linear in its coefficient;
its intersection with the axis group therefore has parameters on one line.
Conversely, normalize a nonzero coordinate of a parameter vector. A second
axis shear, itself of determinant one, takes a coordinate vector to this
normalized vector. The normalization is absorbed into the root coefficient,
so no separate determinant correction is needed. The zero subgroup is handled
by choosing any nonzero coordinate-axis parameter.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed pp.92–93: the full axis group is partitioned by root groups.
-/

public section

open Representation Representation.BinaryOffender Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace RootLines

private def RootFamily (f : G → SpecialLinearGroup (Fin n) F.Carrier) (A : Subgroup G) : Prop :=
  ∃ s : SpecialLinearGroup (Fin n) F.Carrier, ∃ i k : Fin n, ∃ hik : i ≠ k,
    ∀ a ∈ A, ∃ c : F.Carrier, f a = s * SpecialLinearGroup.transvection hik c * s⁻¹

private theorem rootFamily_conjugate (f : G → SpecialLinearGroup (Fin n) F.Carrier)
    (A : Subgroup G) (b : SpecialLinearGroup (Fin n) F.Carrier) :
    RootFamily (fun a => b * f a * b⁻¹) A ↔ RootFamily f A := by
  constructor
  · rintro ⟨s, i, k, hik, hs⟩
    refine ⟨b⁻¹ * s, i, k, hik, ?_⟩
    intro a ha
    obtain ⟨c, hc⟩ := hs a ha
    dsimp only at hc
    refine ⟨c, ?_⟩
    calc
      f a = b⁻¹ * (b * f a * b⁻¹) * b := by group
      _ = b⁻¹ * (s * SpecialLinearGroup.transvection hik c * s⁻¹) * b := by rw [hc]
      _ = _ := by group
  · rintro ⟨s, i, k, hik, hs⟩
    refine ⟨b * s, i, k, hik, ?_⟩
    intro a ha
    obtain ⟨c, hc⟩ := hs a ha
    refine ⟨c, ?_⟩
    dsimp only
    rw [hc]
    group

private theorem inverseTranspose_twice (s : SpecialLinearGroup (Fin n) F.Carrier) :
    SpecialLinearGroup.inverseTranspose (SpecialLinearGroup.inverseTranspose s) = s := by
  change ((SpecialLinearGroup.inverseTranspose s)⁻¹).transpose = s
  rw [← map_inv]
  change ((s⁻¹)⁻¹).transpose.transpose = s
  rw [inv_inv]
  apply Subtype.ext
  rfl

private theorem inverseTranspose_transvection {i k : Fin n} (hik : i ≠ k) (c : F.Carrier) :
    SpecialLinearGroup.inverseTranspose (SpecialLinearGroup.transvection hik c) =
      SpecialLinearGroup.transvection hik.symm (-c) := by
  apply Subtype.ext
  change ((SpecialLinearGroup.transvection hik c)⁻¹).val.transpose = _
  rw [SpecialLinearGroup.transvection_inv]
  simp only [SpecialLinearGroup.transvection_coe, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single]

private theorem rootFamily_inverseTranspose (f : G → SpecialLinearGroup (Fin n) F.Carrier)
    (A : Subgroup G) :
    RootFamily (fun a => SpecialLinearGroup.inverseTranspose (f a)) A ↔ RootFamily f A := by
  have forward (f : G → SpecialLinearGroup (Fin n) F.Carrier)
      (h : RootFamily f A) : RootFamily (fun a => SpecialLinearGroup.inverseTranspose (f a)) A := by
    obtain ⟨s, i, k, hik, hs⟩ := h
    refine ⟨SpecialLinearGroup.inverseTranspose s, k, i, hik.symm, ?_⟩
    intro a ha
    obtain ⟨c, hc⟩ := hs a ha
    refine ⟨-c, ?_⟩
    dsimp only
    rw [hc, map_mul, map_mul, map_inv, inverseTranspose_transvection]
  constructor
  · intro h
    simpa only [inverseTranspose_twice] using forward _ h
  · exact forward f

/-- The recorded basis change and graph automorphism preserve the original root family. -/
theorem inRootGroup_iff_quotient (m : QuotientCoordinates d) (A : Subgroup G) :
    InRootGroup d A ↔
      ∃ s : SpecialLinearGroup (Fin n) F.Carrier, ∃ i k : Fin n, ∃ hik : i ≠ k,
        ∀ a ∈ A, ∃ c : F.Carrier,
          m.action.groupEquiv a = s * SpecialLinearGroup.transvection hik c * s⁻¹ := by
  change RootFamily d.natural.groupEquiv A ↔ RootFamily m.action.groupEquiv A
  rcases m.marking with hm | hm
  · have he : (m.action.groupEquiv : G → SpecialLinearGroup (Fin n) F.Carrier) =
        fun a => m.basisChange * d.natural.groupEquiv a * m.basisChange⁻¹ := funext hm
    rw [he, rootFamily_conjugate]
  · have he : (m.action.groupEquiv : G → SpecialLinearGroup (Fin n) F.Carrier) =
        fun a => m.basisChange * SpecialLinearGroup.inverseTranspose (d.natural.groupEquiv a) *
          m.basisChange⁻¹ := funext hm
    rw [he, rootFamily_conjugate, rootFamily_inverseTranspose]

private theorem conjugate_displacement (s : SpecialLinearGroup (Fin n) F.Carrier)
    {i k : Fin n} (hik : i ≠ k) (c : F.Carrier) :
    (s * SpecialLinearGroup.transvection hik c * s⁻¹).val - 1 =
      c • ((s * SpecialLinearGroup.transvection hik 1 * s⁻¹).val - 1) := by
  have hi : s.val * (s⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel s)
  have hc : Matrix.single i k c = c • Matrix.single i k (1 : F.Carrier) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  change s.val * (1 + Matrix.single i k c) * (s⁻¹).val - 1 =
    c • (s.val * (1 + Matrix.single i k 1) * (s⁻¹).val - 1)
  rw [hc]
  simp only [mul_add, add_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul,
    hi, add_sub_cancel_left]

private theorem shear_parameter (j : Fin n) (w : coordinateHyperplane F n j)
    (s : SpecialLinearGroup (Fin n) F.Carrier) {i k : Fin n} (hik : i ≠ k) (c : F.Carrier)
    (h : shear F n j w = s * SpecialLinearGroup.transvection hik c * s⁻¹) :
    w.val = c • (fun r => ((s * SpecialLinearGroup.transvection hik 1 * s⁻¹).val - 1) r j) := by
  have he := conjugate_displacement s hik c
  rw [← h] at he
  have hw : (shear F n j w).val - 1 = Matrix.vecMulVec w.val (Pi.single j 1) := by
    change 1 + Matrix.vecMulVec w.val (Pi.single j 1) - 1 = _
    exact add_sub_cancel_left _ _
  rw [hw] at he
  funext r
  have hr := congrArg (fun M : Matrix (Fin n) (Fin n) F.Carrier => M r j) he
  simpa only [Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul] using hr

private theorem transvection_apply {i j : Fin n} (hij : i ≠ j) (c : F.Carrier)
    (v : Fin n → F.Carrier) :
    linearNatural F n (SpecialLinearGroup.transvection hij c) v =
      v + (c * v j) • Pi.single i 1 := by
  change (1 + Matrix.single i j c).mulVec v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  congr 1
  funext r
  by_cases hr : r = i <;> simp [hr]

/-- A determinant-one shear carries an elementary root line to any nonzero axis line. -/
theorem shear_line_conjugate (j : Fin n) (w : coordinateHyperplane F n j) (hw : w ≠ 0) :
    ∃ s : SpecialLinearGroup (Fin n) F.Carrier, ∃ i : Fin n, ∃ hij : i ≠ j,
      ∀ c : F.Carrier, ∃ b : F.Carrier,
        shear F n j (c • w) = s * SpecialLinearGroup.transvection hij b * s⁻¹ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, w.val i ≠ 0 := by
    by_contra! h
    exact hw (Subtype.ext (funext h))
  have hj : w.val j = 0 := w.property
  have hij : i ≠ j := by
    rintro rfl
    exact hi hj
  let u : coordinateHyperplane F n i :=
    ⟨(w.val i)⁻¹ • w.val - Pi.single i 1, by
      change (w.val i)⁻¹ * w.val i - (Pi.single i 1 : Fin n → F.Carrier) i = 0
      simp [hi]⟩
  have huj : u.val j = 0 := by
    change (w.val i)⁻¹ * w.val j - (Pi.single i 1 : Fin n → F.Carrier) j = 0
    simp [hj, hij.symm]
  let s := shear F n i u
  refine ⟨s, i, hij, ?_⟩
  intro c
  refine ⟨c * w.val i, ?_⟩
  apply (mul_right_cancel_iff (a := s)).mp
  rw [mul_assoc, inv_mul_cancel, mul_one]
  apply natural_injective F n
  apply LinearMap.ext
  intro v
  simp only [map_mul, Module.End.mul_apply]
  change linearNatural F n (shear F n j (c • w)) (linearNatural F n (shear F n i u) v) =
    linearNatural F n (shear F n i u) (linearNatural F n (SpecialLinearGroup.transvection hij (c * w.val i)) v)
  rw [shear_apply, shear_apply, transvection_apply, shear_apply]
  ext r
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_smul,
    Pi.single_eq_same, huj, mul_zero, add_zero, mul_one]
  change v r + v i * ((w.val i)⁻¹ * w.val r - (Pi.single i 1 : Fin n → F.Carrier) r) +
      v j * (c * w.val r) =
    (v r + (c * w.val i * v j) * (Pi.single i 1 : Fin n → F.Carrier) r) +
      (v i + c * w.val i * v j) *
        ((w.val i)⁻¹ * w.val r - (Pi.single i 1 : Fin n → F.Carrier) r)
  field_simp
  ring

end RootLines
namespace QuotientCoordinates
variable (m : QuotientCoordinates d) (j : Fin n)

/-- The original marked root groups cut out precisely the defining-field parameter lines of Q. -/
theorem rootLineDescription (hn : 3 ≤ n) : m.RootLineDescription j := by
  intro A hA
  constructor
  · intro hroot
    by_cases hbot : A = ⊥
    · let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      obtain ⟨i, hij⟩ := exists_ne j
      let w : coordinateHyperplane F n j := ⟨Pi.single i 1, by
        change (Pi.single i (1 : F.Carrier) : Fin n → F.Carrier) j = 0
        simp [hij.symm]⟩
      refine ⟨w, ?_, ?_⟩
      · intro hw
        have hh := congrArg (fun u : coordinateHyperplane F n j => u.val i) hw
        simp [w] at hh
      · intro a ha
        have ha1 : a = 1 := by simpa only [hbot, Subgroup.mem_bot] using ha
        exact ⟨0, by simp [ha1]⟩
    · obtain ⟨⟨a₀, ha₀⟩, ha₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      obtain ⟨w, hw⟩ := m.exists_axisShear j ⟨a₀, hA ha₀⟩
      change m.axisShear j w = a₀ at hw
      have hwne : w ≠ 0 := by
        intro hz
        apply ha₀ne
        apply Subtype.ext
        change a₀ = 1
        rw [← hw, hz, m.axisShear_zero]
      obtain ⟨s, i, k, hik, hs⟩ := (RootLines.inRootGroup_iff_quotient m A).mp hroot
      obtain ⟨c₀, hc₀⟩ := hs a₀ ha₀
      rw [← hw] at hc₀
      simp only [axisShear, MulEquiv.apply_symm_apply] at hc₀
      have hc₀ne : c₀ ≠ 0 := by
        intro hz
        apply hwne
        apply shear_injective F n j
        simpa only [hz, SpecialLinearGroup.transvection_coeff_zero, mul_one,
          mul_inv_cancel, shear_zero] using hc₀
      have hwexpr := RootLines.shear_parameter j w s hik c₀ hc₀
      refine ⟨w, hwne, ?_⟩
      intro a ha
      obtain ⟨u, hu⟩ := m.exists_axisShear j ⟨a, hA ha⟩
      change m.axisShear j u = a at hu
      obtain ⟨c, hc⟩ := hs a ha
      rw [← hu] at hc
      simp only [axisShear, MulEquiv.apply_symm_apply] at hc
      have huexpr := RootLines.shear_parameter j u s hik c hc
      refine ⟨c * c₀⁻¹, ?_⟩
      rw [← hu]
      congr 1
      apply Subtype.ext
      change (c * c₀⁻¹) • w.val = u.val
      rw [hwexpr, huexpr, smul_smul]
      simp [mul_assoc, hc₀ne]
  · rintro ⟨w, hw, hline⟩
    obtain ⟨s, i, hij, hs⟩ := RootLines.shear_line_conjugate j w hw
    apply (RootLines.inRootGroup_iff_quotient m A).mpr
    refine ⟨s, i, j, hij, ?_⟩
    intro a ha
    obtain ⟨c, hc⟩ := hline a ha
    obtain ⟨b, hb⟩ := hs c
    refine ⟨b, ?_⟩
    rw [← hc]
    simpa only [axisShear, MulEquiv.apply_symm_apply] using hb

end QuotientCoordinates

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
