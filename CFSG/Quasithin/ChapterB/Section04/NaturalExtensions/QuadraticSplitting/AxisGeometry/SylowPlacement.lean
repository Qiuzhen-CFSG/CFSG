module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow placement in the coordinate Levi-axis product

For every supplied quotient marking, the literal product KQ contains a Sylow
2-subgroup of the original actor. A Sylow subgroup of the finite special-linear
matrix group fixes a nonzero vector: its action on the vector space has an even
number of fixed points, one of which is zero. Extend an isomorphism of nonzero
vector spans to a change of basis taking this fixed vector to the selected
coordinate vector. Conjugation by that change of basis preserves determinant
and transports the Sylow subgroup inside the same special-linear group.
Inverse transpose then gives a Sylow subgroup fixing the coordinate functional,
including its scale. The supplied actor equivalence transports it to G, where
`K_sup_Q_eq_coordinateFixer` identifies its containing subgroup with KQ.

This proves the Sylow-placement observation in Aschbacher–Smith B.4.9(1),
printed p.92 (PDF p.103), combined manuscript of 1 March 2004. The argument works
in every dimension admitting the selected coordinate, so in particular covers
all of `SourceFamily`. It needs neither upstairs quadraticity nor fixed lifts,
and derives the needed finiteness from the matrix group itself.
-/

public section

open Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting

private def sylowTranspose (F : BinaryField) (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) F.Carrier →*
      Matrix.SpecialLinearGroup (Fin n) F.Carrier where
  toFun A := A⁻¹.transpose
  map_one' := by apply Subtype.ext; simp [Matrix.SpecialLinearGroup.transpose]
  map_mul' A B := by
    change ((A * B)⁻¹).transpose = (A⁻¹).transpose * (B⁻¹).transpose
    rw [_root_.mul_inv_rev]
    apply Subtype.ext
    exact Matrix.transpose_mul _ _

private theorem sylowTranspose_surjective (F : BinaryField) (n : ℕ) :
    Function.Surjective (sylowTranspose F n) := by
  intro A
  refine ⟨sylowTranspose F n A, ?_⟩
  change ((sylowTranspose F n A)⁻¹).transpose = A
  rw [← map_inv]
  change ((A⁻¹)⁻¹).transpose.transpose = A
  rw [inv_inv]
  apply Subtype.ext
  rfl

private theorem sylow_vector_map {F : BinaryField} {n : ℕ}
    (v w : Fin n → F.Carrier) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : (Fin n → F.Carrier) ≃ₗ[F.Carrier] (Fin n → F.Carrier), e v = w := by
  let ev := LinearEquiv.toSpanNonzeroSingleton F.Carrier _ v hv
  let ew := LinearEquiv.toSpanNonzeroSingleton F.Carrier _ w hw
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ev.symm.trans ew)
  refine ⟨e, ?_⟩
  have h := he (ev 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ev, ew] using h.symm

private theorem exists_sylow_coordinate_vector (F : BinaryField) (n : ℕ) (j : Fin n) :
    ∃ T : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) F.Carrier),
      ∀ g ∈ (T : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)),
        g • (Pi.single j 1 : Fin n → F.Carrier) = Pi.single j 1 := by
  classical
  let P : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) F.Carrier) := Sylow.nonempty.some
  have hcard : 2 ∣ Nat.card (Fin n → F.Carrier) := by
    rw [Nat.card_fun, Nat.card_fin, F.card_eq, ← pow_mul]
    exact dvd_pow_self 2
      (Nat.mul_ne_zero F.degree_pos.ne' (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)))
  have hzero : (0 : Fin n → F.Carrier) ∈ MulAction.fixedPoints P (Fin n → F.Carrier) := by
    intro g
    exact smul_zero g
  obtain ⟨v, hv, hv0⟩ :=
    P.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard hzero
  have he0 : (Pi.single j 1 : Fin n → F.Carrier) ≠ 0 := by
    intro h
    have := congrFun h j
    exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using this)
  obtain ⟨e, he⟩ := sylow_vector_map v (Pi.single j 1) (Ne.symm hv0) he0
  let a : Matrix.SpecialLinearGroup (Fin n) F.Carrier ≃*
      Matrix.SpecialLinearGroup (Fin n) F.Carrier :=
    Matrix.SpecialLinearGroup.toLin'_equiv.trans
      ((_root_.SpecialLinearGroup.congr_linearEquiv e).trans
        Matrix.SpecialLinearGroup.toLin'_equiv.symm)
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective, ?_⟩
  intro g hg
  obtain ⟨g, hgin, rfl⟩ := Subgroup.mem_map.mp hg
  have hfix := hv ⟨g, hgin⟩
  change g • v = v at hfix
  have happ (w : Fin n → F.Carrier) : a g • w = e (g • e.symm w) := by
    change (Matrix.SpecialLinearGroup.toLin'_equiv (a g)) w = _
    change (Matrix.SpecialLinearGroup.toLin'_equiv
      (Matrix.SpecialLinearGroup.toLin'_equiv.symm
        (_root_.SpecialLinearGroup.congr_linearEquiv e
          (Matrix.SpecialLinearGroup.toLin'_equiv g)))) w = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  change a g • (Pi.single j 1 : Fin n → F.Carrier) = Pi.single j 1
  rw [happ, ← he, e.symm_apply_apply, hfix]

private theorem exists_sylow_coordinate_functional (F : BinaryField) (n : ℕ) (j : Fin n) :
    ∃ T : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) F.Carrier),
      ∀ g ∈ (T : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)),
        ∀ v : Fin n → F.Carrier, (g.val *ᵥ v) j = v j := by
  classical
  obtain ⟨P, hP⟩ := exists_sylow_coordinate_vector F n j
  refine ⟨P.mapSurjective (sylowTranspose_surjective F n), ?_⟩
  intro g hg v
  obtain ⟨g, hgin, rfl⟩ := Subgroup.mem_map.mp hg
  have hfix := hP g⁻¹
    ((P : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)).inv_mem hgin)
  change g⁻¹.val *ᵥ (Pi.single j 1 : Fin n → F.Carrier) = Pi.single j 1 at hfix
  have hrow : (sylowTranspose F n g).val j = Pi.single j 1 := by
    ext k
    change g⁻¹.val k j = (Pi.single j (1 : F.Carrier) : Fin n → F.Carrier) k
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hfix k
  change (sylowTranspose F n g).val j ⬝ᵥ v = v j
  rw [hrow]
  simp

open Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace QuotientCoordinates

/-- The literal coordinate Levi-axis product contains a Sylow two-subgroup.
This applies to every supplied marking in the source family, in either quotient
orientation, without any additional hypothesis on the original extension. -/
theorem exists_sylow_le_K_sup_Q (m : QuotientCoordinates d) (j : Fin n) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ m.K j ⊔ m.Q j := by
  classical
  obtain ⟨P, hP⟩ := exists_sylow_coordinate_functional F n j
  refine ⟨P.mapSurjective (f := m.action.groupEquiv.symm.toMonoidHom)
    m.action.groupEquiv.symm.surjective, ?_⟩
  rw [m.K_sup_Q_eq_coordinateFixer]
  intro g hg
  obtain ⟨g, hgin, rfl⟩ := Subgroup.mem_map.mp hg
  intro v
  change linearNatural F n
    (m.action.groupEquiv (m.action.groupEquiv.symm g)) v j = v j
  rw [MulEquiv.apply_symm_apply]
  exact hP g hgin v

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
