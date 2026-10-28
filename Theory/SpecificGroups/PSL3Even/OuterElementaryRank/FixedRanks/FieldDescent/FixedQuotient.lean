module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.FieldTheory.Fixed
import Mathlib.Tactic.Group

/-!
# The whole field fixed subgroup of PSL₃

For any coefficient involution, every fixed projective class has a fixed
special linear representative. Its displacement `k = x⁻¹σ(x)` lies in the
scalar center, so `k³ = 1`; the representative `xk²` is fixed. Matrices fixed
entrywise are exactly the special linear matrices over the actual fixed
subfield. Coefficient inclusion has precisely the smaller scalar center as
its projective kernel, hence induces the desired PSL₃ equivalence.

This extends the checked quartic calculation in
`PSL3Four.CentralCover.FixedResiduals.ProjectiveField` without assuming that
the smaller center is trivial. Source: GLS3, Theorem 2.5.12 and §2.7;
Aschbacher–Smith, 16.1.4(4), printed p.1171. No residual is taken here.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
variable {F : Type*} [Field F]

private theorem central_cube (x : SL(3,F)) (hx : x ∈ center SL(3,F)) : x ^ 3 = 1 := by
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hx
  have hr' : r ^ 3 = 1 := hr
  apply Subtype.ext
  change x.val ^ 3 = (1 : Matrix (Fin 3) (Fin 3) F)
  rw [← he]
  change (Matrix.diagonal (fun _ : Fin 3 => r)) ^ 3 = _
  simp only [Matrix.diagonal_pow]
  congr 1
  funext i
  exact hr'

/-- Every projective fixed point has an entrywise fixed SL₃ representative. -/
theorem field_fixed_representative (σ : F ≃+* F) (hs : σ ^ 2 = 1)
    (b : (fieldAction F σ).fixedSubgroup) :
    ∃ x : SL(3,F), Atlas.fieldEquivSL 3 σ x = x ∧
      QuotientGroup.mk' (center SL(3,F)) x = b.val := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) b.val
  let a := Atlas.fieldEquivSL 3 σ
  have ha (y : SL(3,F)) : a (a y) = y := by
    ext i j
    exact DFunLike.congr_fun hs (y i j)
  let k := x⁻¹ * a x
  have hk : (QuotientGroup.mk' (center SL(3,F))) k = 1 := by
    dsimp only [k]
    rw [map_mul, map_inv]
    rw [← Atlas.fieldEquivPSL_mk 3 σ]
    change (QuotientGroup.mk' _ x)⁻¹ * fieldAction F σ (QuotientGroup.mk' _ x) = 1
    rw [hx, (MulAut.mem_fixedSubgroup _ _).mp b.property, inv_mul_cancel]
  have hk3 : k ^ 3 = 1 := central_cube k ((QuotientGroup.eq_one_iff k).mp hk)
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hck : a k = k⁻¹ := by simp [k, map_mul, map_inv, ha]
  have hcx : a x = x * k := by simp [k]
  have hz : a (x * k ^ 2) = x * k ^ 2 := by
    rw [map_mul, map_pow, hck, hcx]
    calc
      x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
      _ = x * k ^ 2 := by rw [hki]
  exact ⟨x * k ^ 2, hz, by simp [map_mul, map_pow, hk, hx]⟩

private def fixedHom (σ : F ≃+* F) :
    SL(3, FixedBy.subfield F σ) →* (fieldAction F σ).fixedSubgroup :=
  ((QuotientGroup.mk' (center SL(3,F))).comp
    (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype)).codRestrict _ (by
      intro x
      rw [MulAut.mem_fixedSubgroup]
      change fieldAction F σ (QuotientGroup.mk _) = QuotientGroup.mk _
      rw [fieldAction_mk]
      congr 1
      ext i j
      exact (x i j).property)

private theorem fixedHom_surjective (σ : F ≃+* F) (hs : σ ^ 2 = 1) :
    Function.Surjective (fixedHom σ) := by
  intro b
  obtain ⟨x, hx, hq⟩ := field_fixed_representative σ hs b
  let K := FixedBy.subfield F σ
  let M : Matrix (Fin 3) (Fin 3) K := fun i j =>
    ⟨x i j, congrArg (fun z : SL(3,F) => z i j) hx⟩
  have hM : M.map K.subtype = x.val := rfl
  have hd : M.det = 1 := by
    apply K.subtype.injective
    rw [K.subtype.map_det, map_one]
    change (M.map K.subtype).det = 1
    rw [hM]
    exact x.property
  refine ⟨⟨M, hd⟩, ?_⟩
  apply Subtype.ext
  exact hq

private theorem fixedHom_ker (σ : F ≃+* F) :
    (fixedHom σ).ker = center SL(3, FixedBy.subfield F σ) := by
  let K := FixedBy.subfield F σ
  let f : SL(3,K) →* SL(3,F) := SpecialLinearGroup.map K.subtype
  have hf : Function.Injective f := by
    intro x y h
    ext i j
    exact congrArg (fun z : SL(3,F) => z i j) h
  have hm (x : SL(3,K)) : x ∈ (fixedHom σ).ker ↔ f x ∈ center SL(3,F) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp
        (congrArg (fun z : (fieldAction F σ).fixedSubgroup => z.val) h)
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr h
  ext x
  rw [hm]
  constructor
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply hf
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hx (f y)
  · intro hx
    obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hx
    apply SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨K.subtype r, ?_, ?_⟩
    · simpa only [map_pow, map_one] using congrArg K.subtype hr
    · change Matrix.scalar (Fin 3) (K.subtype r) = x.val.map K.subtype
      rw [← he]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.diagonal, hij]

/-- The whole pure-field fixed subgroup is PSL₃ over the literal fixed subfield.
The argument requires only involutivity, and includes the binary fixed field. -/
noncomputable def pure_field_fixed_equiv (σ : F ≃+* F) (hs : σ ^ 2 = 1) :
    (fieldAction F σ).fixedSubgroup ≃* PSL(3, FixedBy.subfield F σ) :=
  (QuotientGroup.liftEquiv (center SL(3, FixedBy.subfield F σ))
    (fixedHom_surjective σ hs) (fixedHom_ker σ).symm).symm

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
