module
public import ABG.ChapterII.Section2.UnitarySemilinear
public import GorensteinWalter.PGL2HomRigidity
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Coefficient compatibility of the prescribed unitary projective map

For an odd prime p and nonzero n, let q map the actual Hermitian determinant
level SU2Level m to PGL2(GF(p^n)), with the canonical formula on level zero
through a supplied special-unitary to special-linear equivalence eSU.
Suppose a quadratic-field automorphism σ and a base-field automorphism τ
intertwine through eSU on actual special-unitary matrices. Then q takes
σ-related matrices in the full level to τ-related projective elements.
This includes every determinant level; neither surjectivity of q nor an
additional abstract coefficient action is assumed.

Restrict the existing GU2 coefficient equivalence to a homomorphism c on
the actual determinant level, using the proved membership invariance.
The canonical level-zero image of q is the standard PSL2 range. On this
normal subgroup, the supplied matrix intertwining and projective coefficient
naturality show agreement of q and τ⁻¹ composed with q composed with c.
The trivial centralizer of the PSL2 range then forces these homomorphisms
to agree everywhere. The pointwise conclusion follows through the original
nested GU2 and GL2 subtype inclusions.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pages 27-28,
the coefficient action in the unitary model. The intertwining hypothesis
is exactly the matrix statement supplied by
`exists_specialUnitary_equiv_sl2_of_odd_coefficients`; thus the odd-subgroup
construction feeds this result without changing the chosen eSU or action.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem unitary_model_projection_coefficients
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0) (m : ℕ)
    (q : SU2Level p n hn m →* PGL2 (GaloisField p n))
    (eSU : (unitaryForm 2 p n hn).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))
    (hq : ∀ a : SU2Level p n hn 0,
      q ⟨a.val, SU2Level_mono p n hn (Nat.zero_le m) a.property⟩ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL
          (sl2ProjectiveProjection (GaloisField p n) (eSU (SU2LevelZeroEquivSpecial p n hn a))))
    (σ : GaloisField p (2 * n) ≃+* GaloisField p (2 * n))
    (τ : GaloisField p n ≃+* GaloisField p n)
    (hcoeff : ∀ x y : (unitaryForm 2 p n hn).specialSubgroup,
      y.val = coefficientEquiv σ x.val → eSU y = sl2RingEquiv τ (eSU x))
    (x y : SU2Level p n hn m)
    (hxy : y.val.val = coefficientEquiv σ x.val.val) :
    q y = pgl2FieldAut (GaloisField p n) τ (q x) := by
  let F := GaloisField p n
  let D := SU2Level p n hn m
  let K := SU2Level p n hn 0
  let N := K.subgroupOf D
  have hKD : K ≤ D := SU2Level_mono p n hn (Nat.zero_le m)
  let c : D →* D := ((GU2CoefficientEquiv p n hn σ).toMonoidHom.comp D.subtype).codRestrict D
    (fun z => (GU2CoefficientAction_mem_SU2Level_iff p n hn m σ z.val).mpr z.property)
  let t := pgl2FieldAut F τ
  let r : D →* PGL2 F := t.symm.toMonoidHom.comp (q.comp c)
  let e0 : K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (SU2LevelZeroEquivSpecial p n hn).trans eSU
  have hmap : N.map q = Matrix.ProjectiveSpecialLinearGroup.toPGL.range := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨sl2ProjectiveProjection F (e0 ⟨a.val, ha⟩), (hq ⟨a.val, ha⟩).symm⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨a, ha⟩ := (sl2ProjectiveProjection_surjective F).comp e0.surjective z
      exact ⟨⟨a.val, hKD a.property⟩, a.property,
        (hq a).trans (congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL ha)⟩
  have hagree (a : N) : q a = r a := by
    let a0 : K := ⟨a.val.val, a.property⟩
    let b0 : K := ⟨GU2CoefficientEquiv p n hn σ a0.val,
      (GU2CoefficientAction_mem_SU2Level_iff p n hn 0 σ a0.val).mpr a0.property⟩
    have hval (z : K) : z.val.val = (SU2LevelZeroEquivSpecial p n hn z).val := by
      simpa only [MulEquiv.symm_apply_apply] using
        SU2LevelZeroEquivSpecial_symm_val p n hn (SU2LevelZeroEquivSpecial p n hn z)
    have hab : e0 b0 = sl2RingEquiv τ (e0 a0) := by
      apply hcoeff
      change (SU2LevelZeroEquivSpecial p n hn b0).val =
        coefficientEquiv σ (SU2LevelZeroEquivSpecial p n hn a0).val
      rw [← hval b0, ← hval a0]
      rfl
    have hnat : sl2ProjectiveProjection F (sl2RingEquiv τ (e0 a0)) =
        psl2FieldAut F τ (sl2ProjectiveProjection F (e0 a0)) := by
      simp only [psl2FieldAut_apply, sl2ProjectiveProjection, psl2RingEquiv_mk]
      congr 1
      ext i j
      simp only [sl2RingEquiv_apply_entry]
      rfl
    apply t.injective
    change t (q a.val) = t (t.symm (q (c a.val)))
    rw [t.apply_symm_apply]
    change t (q ⟨a0.val, hKD a0.property⟩) = q ⟨b0.val, hKD b0.property⟩
    rw [hq a0, hq b0]
    change t (Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection F (e0 a0))) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection F (e0 b0))
    rw [hab, hnat, psl2FieldAut_toPGL]
  have hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, n, Fact.out, hp, Nat.pos_of_ne_zero hn, GaloisField.card p n hn⟩
  have heq := pgl2_hom_eq_of_agree_on_normal_psl2 hF q r N hagree hmap
  have hy : y = c x := by
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  rw [hy]
  have hh := congrArg t (DFunLike.congr_fun heq x)
  exact ((show t (q x) = t (t.symm (q (c x))) from hh).trans (t.apply_symm_apply _)).symm

end ABG
