module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldAction
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.ModelBounds
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# Whole fixed groups of graph-field involutions of PSL₃

The literal actor `linearConj g * fieldAction σ * graph` fixes precisely a
projective special unitary group for a genuine Hermitian form with conjugation
`σ`. No conjugacy or model-identification hypothesis is needed.

Faithfulness of the central-quotient action lifts the square-one identity to
SL₃. The square of the actor makes `g * σ(g⁻ᵀ)` scalar, with scalar of norm
one. Elementary scalar Hilbert 90 supplies a nonzero `t` for which `t • g⁻¹`
is Hermitian. An SL₃ matrix is exactly fixed if and only if it preserves this
form. Every projective fixed point has an exactly fixed lift: its central
discrepancy `k` has cube one, and multiplying the lift by `k²` corrects it.
The injective map PSL₃ → PGL₃ consequently identifies the whole fixed group
with the literal projective SU image, retaining its scalar kernel.

The rank application uses the existing fixed-field parameter and unitary rank
calculations. It includes fixed-field order two, where the whole projective
unitary group has order 72; no two-residual is substituted.

Sources: GLS3, Theorem 2.5.12 and §2.7 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith E.1.14(1), printed p.214, and the graph-field case of 16.1.4,
printed p.1171. The scalar lifting argument follows the checked graph case
in `Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph`; the elementary
scalar descent calculation also occurs in the unitary `Descent.LinearCocycle`
development. SL₃ perfectness is reused through the attributed ATLAS port
imported by `FixedRanks.FieldAction`.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.OuterSolvable BenderSuzuki.MatrixGroups
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphFieldDescent
variable {F : Type*} [Field F]

private theorem centerAction_injective : Function.Injective (centerAction F) := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have he : centerAction F = Subgroup.quotientAut (center SL(3,F)) := by
    ext a x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) x
    change centerAction F a (QuotientGroup.mk y) = _
    rw [centerAction_mk, Subgroup.quotientAut_apply_mk]
    rfl
  rw [he]
  exact MulAut.quotient_center_injective

private theorem linearConj_eq_one_scalar (g : GL (Fin 3) F)
    (hg : linearConj F g = 1) : ∃ u : Fˣ, GeneralLinearGroup.scalar (Fin 3) u = g := by
  have hs : linearConjSL F g = 1 := centerAction_injective (hg.trans (map_one _).symm)
  have hc (x : SL(3,F)) : g * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * g := by
    have he := congrArg SpecialLinearGroup.toGL (DFunLike.congr_fun hs x)
    rw [linearConjSL_toGL] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hz : g ∈ center (GL (Fin 3) F) := by
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact (congrArg Units.val (hc ⟨t.toMatrix, by simp⟩)).symm
  rwa [GeneralLinearGroup.center_eq_range_scalar] at hz

private def twistGL (σ : F ≃+* F) : GL (Fin 3) F →* GL (Fin 3) F :=
  (GeneralLinearGroup.map σ.toRingHom).comp (inverseTransposeGL F)

private theorem twistGL_twice (σ : F ≃+* F) (hσ : σ ^ 2 = 1) (g : GL (Fin 3) F) :
    twistGL σ (twistGL σ g) = g := by
  have hi (x : F) : σ (σ x) = x := DFunLike.congr_fun hσ x
  apply Units.ext
  ext i j
  exact hi (g.val i j)

private theorem twistGL_scalar (σ : F ≃+* F) (u : Fˣ) :
    twistGL σ (GeneralLinearGroup.scalar (Fin 3) u) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom u)⁻¹ := by
  apply Units.ext
  ext i j
  change σ ((GeneralLinearGroup.scalar (Fin 3) u).inv j i) = _
  by_cases hij : i = j <;> simp [GeneralLinearGroup.scalar, Matrix.scalar_apply,
    hij, eq_comm]

private theorem scalar_injective : Function.Injective (GeneralLinearGroup.scalar (Fin 3) (R := F)) := by
  intro u v h
  apply Units.ext
  exact congrArg (fun g : GL (Fin 3) F => g.val 0 0) h

private theorem scalar_norm (σ : F ≃+* F) (hσ : σ ^ 2 = 1)
    (g : GL (Fin 3) F) (u : Fˣ)
    (hu : GeneralLinearGroup.scalar (Fin 3) u = g * twistGL σ g) :
    σ (u : F) * (u : F) = 1 := by
  have ht := congrArg (twistGL σ) hu
  rw [twistGL_scalar, map_mul, twistGL_twice σ hσ] at ht
  have hs : twistGL σ g * g = GeneralLinearGroup.scalar (Fin 3) u := by
    apply mul_left_cancel (a := g)
    rw [← mul_assoc, ← hu, GeneralLinearGroup.scalar_commute]
  rw [hs] at ht
  have h := scalar_injective ht
  have h' : (Units.map σ.toMonoidHom u) * u = 1 := by
    calc _ = (Units.map σ.toMonoidHom u) * (Units.map σ.toMonoidHom u)⁻¹ :=
               congrArg (fun z => (Units.map σ.toMonoidHom u) * z) h.symm
         _ = 1 := mul_inv_cancel _
  exact congrArg Units.val h'

private theorem scalar_parameter (σ : F ≃+* F) (hi : Function.Involutive σ)
    (hne : σ ≠ 1) (k : F) (hk : σ k * k = 1) :
    ∃ t : F, t ≠ 0 ∧ σ t * k = t := by
  have hn : ∃ s : F, σ s ≠ s := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  by_cases hkneg : k = -1
  · obtain ⟨s, hs⟩ := hn
    refine ⟨s - σ s, sub_ne_zero.mpr (Ne.symm hs), ?_⟩
    rw [hkneg, map_sub, hi]
    ring
  · refine ⟨1 + k, ?_, ?_⟩
    · intro h
      apply hkneg
      linear_combination h
    · rw [map_add, map_one, add_mul, one_mul, hk, add_comm]

private def actorSL (g : GL (Fin 3) F) (σ : F ≃+* F) : MulAut SL(3,F) :=
  linearConjSL F g * Atlas.fieldEquivSL 3 σ * graphSL F

private theorem actorSL_projective (g : GL (Fin 3) F) (σ : F ≃+* F) :
    centerAction F (actorSL g σ) = linearConj F g * fieldAction F σ * graph F := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) x
  simp only [QuotientGroup.mk'_apply, MulAut.mul_apply, centerAction_mk,
    graph_mk, fieldAction_mk, linearConj_mk]
  rfl

private theorem actorSL_sq (g : GL (Fin 3) F) (σ : F ≃+* F)
    (h : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1) :
    actorSL g σ ^ 2 = 1 := by
  apply centerAction_injective
  rw [map_pow, actorSL_projective, h, map_one]

private theorem actorSL_toGL (g : GL (Fin 3) F) (σ : F ≃+* F) (x : SL(3,F)) :
    SpecialLinearGroup.toGL (actorSL g σ x) =
      g * twistGL σ (SpecialLinearGroup.toGL x) * g⁻¹ := by
  rw [show actorSL g σ x = linearConjSL F g (Atlas.fieldEquivSL 3 σ (graphSL F x)) from rfl,
    linearConjSL_toGL]
  congr 2
  apply Units.ext
  change ((SpecialLinearGroup.transpose x)⁻¹).val.map σ =
    (SpecialLinearGroup.toGL x).inv.transpose.map σ
  congr 1
  exact (Matrix.adjugate_transpose x.val).symm

private theorem exists_gram (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (h : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1) :
    ∃ (J : HermitianForm 3 F) (t : F), J.conj = σ ∧ t ≠ 0 ∧ J.form = t • g.inv := by
  have hσ := graphField_part_sq g σ h
  have hi : Function.Involutive σ := fun x => DFunLike.congr_fun hσ x
  have hlin : linearConj F (g * twistGL σ g) = 1 := by
    rw [graphField_sq, hσ, map_one, mul_one] at h
    exact h
  obtain ⟨u, hu⟩ := linearConj_eq_one_scalar _ hlin
  obtain ⟨t, ht, htu⟩ := scalar_parameter σ hi hne u (scalar_norm σ hσ g u hu)
  have hadj : twistGL σ g = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) u := by
    rw [hu, inv_mul_cancel_left]
  have he (i j : Fin 3) : σ (g.inv j i) = g.inv i j * (u : F) := by
    have hh := congrArg (fun z : GL (Fin 3) F => z.val i j) hadj
    change σ (g.inv j i) = (g.inv * Matrix.scalar (Fin 3) (u : F)) i j at hh
    simpa [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] using hh
  refine ⟨⟨σ, hi, t • g.inv, ?_, ?_⟩, t, rfl, ht, rfl⟩
  · intro i j
    change σ (t * g.inv j i) = t * g.inv i j
    rw [map_mul, he]
    calc σ t * (g.inv i j * ↑u) = (σ t * ↑u) * g.inv i j := by ring
         _ = t * g.inv i j := by rw [htu]
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ht) (GeneralLinearGroup.det_ne_zero g⁻¹)

private theorem fixed_representative (g : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1)
    (b : (linearConj F g * fieldAction F σ * graph F).fixedSubgroup) :
    ∃ x : (actorSL g σ).fixedSubgroup, QuotientGroup.mk' (center SL(3,F)) x.val = b.val := by
  let q := QuotientGroup.mk' (center SL(3,F))
  let a := actorSL g σ
  have ha (x : SL(3,F)) : a (a x) = x := DFunLike.congr_fun (actorSL_sq g σ hs) x
  have hq (x : SL(3,F)) : q (a x) =
      (linearConj F g * fieldAction F σ * graph F) (q x) := by
    rw [← actorSL_projective]
    rfl
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) b.val
  let k := x⁻¹ * a x
  have hk : q k = 1 := by
    change q (x⁻¹ * a x) = 1
    rw [map_mul, map_inv, hq, hx, (MulAut.mem_fixedSubgroup _ _).mp b.property,
      inv_mul_cancel]
  have hkz : k ∈ center SL(3,F) := (QuotientGroup.eq_one_iff k).mp hk
  have hk3 : k ^ 3 = 1 := by
    obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hkz
    apply Subtype.ext
    change k.val ^ 3 = 1
    rw [← he, ← map_pow, (by simpa using hr : r ^ 3 = 1), map_one]
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hak : a k = k⁻¹ := by simp [k, map_mul, map_inv, ha]
  have hax : a x = x * k := by simp [k]
  have hz : a (x * k ^ 2) = x * k ^ 2 := by
    rw [map_mul, map_pow, hak, hax]
    calc x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
         _ = x * k ^ 2 := by rw [hki]
  exact ⟨⟨x * k ^ 2, (MulAut.mem_fixedSubgroup _ _).mpr hz⟩,
    by change q (x * k ^ 2) = _; rw [map_mul, map_pow, hk, hx]; simp⟩

private theorem fixed_iff_unitary (g : GL (Fin 3) F) (σ : F ≃+* F)
    (J : HermitianForm 3 F) (t : F) (hJ : J.conj = σ) (ht : t ≠ 0)
    (hform : J.form = t • g.inv) (x : SL(3,F)) :
    actorSL g σ x = x ↔ SpecialLinearGroup.toGL x ∈ J.specialSubgroup := by
  let A := SpecialLinearGroup.toGL x
  have hct : J.conjTranspose A.val = (twistGL σ A)⁻¹.val := by
    ext i j
    change J.conj (A.val j i) = σ (A.val j i)
    rw [hJ]
  rw [J.mem_specialSubgroup_iff]
  simp only [SpecialLinearGroup.coeToGL_det, and_true]
  change actorSL g σ x = x ↔ J.conjTranspose A.val * J.form * A.val = J.form
  rw [hform, Matrix.mul_smul, Matrix.smul_mul, (smul_right_injective _ ht).eq_iff, hct]
  constructor
  · intro hx
    have he : g * twistGL σ A * g⁻¹ = A :=
      (actorSL_toGL g σ x).symm.trans (congrArg SpecialLinearGroup.toGL hx)
    have hm : (twistGL σ A)⁻¹ * g⁻¹ * A = g⁻¹ := by
      calc _ = (twistGL σ A)⁻¹ * g⁻¹ * (g * twistGL σ A * g⁻¹) :=
                 congrArg (fun z => (twistGL σ A)⁻¹ * g⁻¹ * z) he.symm
           _ = g⁻¹ := by group
    exact congrArg Units.val hm
  · intro hx
    have he : (twistGL σ A)⁻¹ * g⁻¹ * A = g⁻¹ := Units.ext hx
    apply SpecialLinearGroup.toGL_injective
    rw [actorSL_toGL]
    change g * twistGL σ A * g⁻¹ = A
    calc _ = g * twistGL σ A * ((twistGL σ A)⁻¹ * g⁻¹ * A) := by rw [he]
         _ = A := by group

private def fixedToUnitary (g : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1)
    (J : HermitianForm 3 F) (t : F) (hJ : J.conj = σ) (ht : t ≠ 0)
    (hform : J.form = t • g.inv) :
    (linearConj F g * fieldAction F σ * graph F).fixedSubgroup →*
      ProjectiveSpecialUnitaryMatrixGroup J :=
  (ProjectiveSpecialLinearGroup.toPGL.comp
    (linearConj F g * fieldAction F σ * graph F).fixedSubgroup.subtype).codRestrict _ (by
      intro b
      obtain ⟨x, hx⟩ := fixed_representative g σ hs b
      refine ⟨SpecialLinearGroup.toGL x.val,
        (fixed_iff_unitary g σ J t hJ ht hform x.val).mp
          ((MulAut.mem_fixedSubgroup _ _).mp x.property), ?_⟩
      exact congrArg ProjectiveSpecialLinearGroup.toPGL hx)

private theorem fixedToUnitary_bijective (g : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1)
    (J : HermitianForm 3 F) (t : F) (hJ : J.conj = σ) (ht : t ≠ 0)
    (hform : J.form = t • g.inv) :
    Function.Bijective (fixedToUnitary g σ hs J t hJ ht hform) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact ProjectiveSpecialLinearGroup.toPGL_injective (congrArg Subtype.val he)
  · rintro ⟨b, A, hA, rfl⟩
    have hd : GeneralLinearGroup.det A = 1 := (J.mem_specialSubgroup_iff A).mp hA |>.2
    let x := (slEquivDetKernel F).symm ⟨A, hd⟩
    have hxGL : SpecialLinearGroup.toGL x = A := slEquivDetKernel_symm_toGL F ⟨A, hd⟩
    have hx : actorSL g σ x = x :=
      (fixed_iff_unitary g σ J t hJ ht hform x).mpr (hxGL.symm ▸ hA)
    have hq : QuotientGroup.mk' (center SL(3,F)) x ∈
        (linearConj F g * fieldAction F σ * graph F).fixedSubgroup := by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      rw [← actorSL_projective]
      change QuotientGroup.mk (actorSL g σ x) = QuotientGroup.mk x
      rw [hx]
    refine ⟨⟨QuotientGroup.mk' (center SL(3,F)) x, hq⟩, Subtype.ext ?_⟩
    change ProjGenLinGroup.mk (SpecialLinearGroup.toGL x) = ProjGenLinGroup.mk A
    rw [hxGL]

/-- Every literal graph-field involution has its whole fixed subgroup
isomorphic to the projective special unitary group of a genuine Hermitian form. -/
theorem exists_fixed_equiv_unitary (g : GL (Fin 3) F) (σ : F ≃+* F)
    (hne : σ ≠ 1) (hs : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1) :
    ∃ J : HermitianForm 3 F, J.conj = σ ∧
      Nonempty ((linearConj F g * fieldAction F σ * graph F).fixedSubgroup ≃*
        ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨J, t, hJ, ht, hform⟩ := exists_gram g σ hne hs
  exact ⟨J, hJ, ⟨MulEquiv.ofBijective (fixedToUnitary g σ hs J t hJ ht hform)
    (fixedToUnitary_bijective g σ hs J t hJ ht hform)⟩⟩

/-- The full mixed fixed group has the required sharper two-rank bound,
including degree two over the prime field. -/
theorem fixed_rank_le [Finite F] {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hs : (linearConj F g * fieldAction F σ * graph F) ^ 2 = 1) :
    primeRank 2 (linearConj F g * fieldAction F σ * graph F).fixedSubgroup ≤ f - 1 := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := exists_fixed_equiv_unitary g σ hne hs
  exact graphField_fixed_rank_of_equiv hf hF _ σ (graphField_part_sq g σ hs) hne J hJ e

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphFieldDescent
