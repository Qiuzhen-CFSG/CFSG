module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Geometry

/-!
# The actual scalar torus in the three-dimensional quotient

The homomorphism a ↦ diag(a,a,a⁻²), with the exceptional entry at the
chosen coordinate, constructs the scalar torus inside the actual actor G.
It is cyclic of odd order 2^degree - 1 and preserves both the quotient axis
and the complementary line. Their full simultaneous stabilizer normalizes
both Q and K. All coordinates belong to the quotient model, not to V.

Source: Aschbacher–Smith B.4.9(1), printed p.93 (1 March 2004 manuscript).
Identification with the centralizer of K in the full Levi and the full-Levi
factorization remain separate matrix calculations.
-/

@[expose] public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
variable (F : BinaryField) (j : Fin 3)
/-- Scalar a on the axis and a⁻² on its complementary line. -/
noncomputable def oppositeScalarMatrix (a : F.Carrierˣ) :
    Matrix.SpecialLinearGroup (Fin 3) F.Carrier :=
  ⟨Matrix.diagonal (fun i => if i = j then (↑a⁻¹ : F.Carrier)^2 else ↑a), by
    rw [Matrix.det_diagonal]
    fin_cases j <;> simp [Fin.prod_univ_succ, pow_two, mul_left_comm]⟩
/-- The actual diagonal torus homomorphism into SL₃. -/
noncomputable def oppositeScalarHom : F.Carrierˣ →*
    Matrix.SpecialLinearGroup (Fin 3) F.Carrier where
  toFun := oppositeScalarMatrix F j
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal _ = 1
    simp
  map_mul' a b := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i = j <;> simp [hi, mul_pow, mul_comm]



theorem oppositeScalarHom_injective : Function.Injective (oppositeScalarHom F j) := by
  intro a b h
  obtain ⟨i,hi⟩ := exists_ne j
  have he := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F.Carrier => g.val i i) h
  apply Units.ext
  change Matrix.diagonal (fun i => if i = j then (↑a⁻¹ : F.Carrier)^2 else ↑a) i i =
    Matrix.diagonal (fun i => if i = j then (↑b⁻¹ : F.Carrier)^2 else ↑b) i i at he
  simpa only [Matrix.diagonal_apply_eq, if_neg hi] using he

theorem oppositeScalarMatrix_apply (a : F.Carrierˣ) (z : Fin 3 → F.Carrier)
    (i : Fin 3) :
    linearNatural F 3 (oppositeScalarMatrix F j a) z i =
      (if i = j then (↑a⁻¹ : F.Carrier)^2 else ↑a) * z i := by
  change (Matrix.diagonal _).mulVec z i = _
  exact Matrix.mulVec_diagonal _ _ _

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F} {ρ : Representation (ZMod 2) G V} {d : DoubleNatural F 3 ρ}
  (m : QuotientCoordinates d)
namespace QuotientCoordinates

/-- The simultaneous stabilizer of the actual quotient axis and line. -/
noncomputable def oppositeFullLevi (j : Fin 3) : Subgroup G :=
  subspaceStabilizer d.space.quotientRepresentation (m.axis j) ⊓
    subspaceStabilizer d.space.quotientRepresentation (m.line j)

/-- Pull the scalar matrices back through the supplied actor marking. -/
noncomputable def oppositeTorusHom (j : Fin 3) : F.Carrierˣ →* G :=
  m.action.groupEquiv.symm.toMonoidHom.comp (oppositeScalarHom F j)

/-- The scalar torus as an actual subgroup of G. -/
noncomputable def oppositeTorus (j : Fin 3) : Subgroup G := (m.oppositeTorusHom j).range

theorem oppositeTorusHom_injective : Function.Injective (m.oppositeTorusHom j) :=
  m.action.groupEquiv.symm.injective.comp (oppositeScalarHom_injective F j)

noncomputable def oppositeTorusEquiv : F.Carrierˣ ≃* m.oppositeTorus j :=
  MonoidHom.ofInjective (m.oppositeTorusHom_injective j)

instance oppositeTorus_finite : Finite (m.oppositeTorus j) :=
  Finite.of_equiv F.Carrierˣ (m.oppositeTorusEquiv j).toEquiv

theorem oppositeTorus_card : Nat.card (m.oppositeTorus j) = 2^F.degree-1 := by
  rw [← Nat.card_congr (m.oppositeTorusEquiv j).toEquiv, Nat.card_units, F.card_eq]

theorem oppositeTorus_odd : Odd (Nat.card (m.oppositeTorus j)) := by
  rw [m.oppositeTorus_card j]
  apply Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
  · exact even_two.pow_of_ne_zero F.degree_pos.ne'
  · exact odd_one

theorem oppositeTorus_cyclic : IsCyclic (m.oppositeTorus j) :=
  (m.oppositeTorusEquiv j).isCyclic.mp inferInstance



theorem oppositeTorusHom_marking (a : F.Carrierˣ) :
    m.action.groupEquiv (m.oppositeTorusHom j a) = oppositeScalarMatrix F j a :=
  m.action.groupEquiv.apply_symm_apply _

theorem oppositeTorus_le_fullLevi : m.oppositeTorus j ≤ m.oppositeFullLevi j := by
  apply le_inf
  · apply le_subspaceStabilizer
    rintro _ ⟨a,rfl⟩ z hz
    apply (m.largeField_mem_axis j _).mpr
    rw [m.action.intertwines, m.oppositeTorusHom_marking j,
      oppositeScalarMatrix_apply, if_pos rfl, (m.largeField_mem_axis j z).mp hz, mul_zero]
  · apply le_subspaceStabilizer
    rintro _ ⟨a,rfl⟩ z hz
    obtain ⟨c,hc⟩ := (m.largeField_mem_line j z).mp hz
    apply (m.largeField_mem_line j _).mpr
    refine ⟨(↑a⁻¹ : F.Carrier)^2*c, ?_⟩
    rw [m.action.intertwines, m.oppositeTorusHom_marking j, ← hc]
    funext i
    rw [oppositeScalarMatrix_apply]
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi]

theorem oppositeFullLevi_normalizes_Q :
    m.oppositeFullLevi j ≤ Subgroup.normalizer (m.Q j) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro k hk q hq
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro z hz
  have hk' := (m.oppositeFullLevi j).inv_mem hk
  have hi : d.space.quotientRepresentation k⁻¹ z ∈ m.axis j := (hk'.1 z).mpr hz
  change d.space.quotientRepresentation (k*q*k⁻¹) z = z
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hq.2 _ hi]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem oppositeFullLevi_normalizes_K :
    m.oppositeFullLevi j ≤ Subgroup.normalizer (m.K j) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro k hk x hx
  refine ⟨?_, Subgroup.mem_top _, ?_⟩
  · exact (subspaceStabilizer d.space.quotientRepresentation (m.axis j)).mul_mem
      ((subspaceStabilizer d.space.quotientRepresentation (m.axis j)).mul_mem hk.1 hx.1)
      ((subspaceStabilizer d.space.quotientRepresentation (m.axis j)).inv_mem hk.1)
  · intro z hz
    have hk' := (m.oppositeFullLevi j).inv_mem hk
    have hi : d.space.quotientRepresentation k⁻¹ z ∈ m.line j := (hk'.2 z).mpr hz
    change d.space.quotientRepresentation (k*x*k⁻¹) z = z
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.2.2 _ hi]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
