module
public import Theory.GroupAction.SymplecticRankThree.TranslationGroup
public import Mathlib.Algebra.Group.TransferInstance

/-!
# Additive line equations in the reconstructed affine chart

The geometric translations parallel to a direction form a subgroup of order
q. Evaluation identifies it with the corresponding actual axis. Every affine
line is a coset of this subgroup in the regular abelian translation group.
Transferring that group's addition to the actual affine points therefore
makes the origin zero and gives the literal line equation a ∈ b+L_d iff
a-b ∈ L_d. No additive operations, translation action or coordinate formula
is assumed.

Source: the coordinatization step in Higman (1964), Lemma 10, pp.153–154.
This proves the additive structure behind the chart. Constructing field
multiplication and extending to projective field coordinates remain necessary
for the nonbinary recognition theorem.
-/

public noncomputable section
open scoped IsMulCommutative
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

/-- A translation is in a direction exactly when its origin image is on that axis. -/
theorem translation_direction_iff (T : f.translations hl hq) (d : f.Direction hl hq) :
    T.val.HasDirection d ↔ (f.translationEquiv hl hq T : Ω) ∈ D.line d f.origin := by
  constructor
  · intro hT
    exact T.val.direction_spec hT (f.planeOrigin hl hq)
  · intro hTd
    obtain ⟨e,he⟩ := T.val.translation_spec.mp T.property
    by_cases hed : e = d
    · exact hed ▸ he
    have hed' : (e : Ω) ≠ d := fun hh => hed (Subtype.ext hh)
    have hTo : T.val.val (f.planeOrigin hl hq) = f.planeOrigin hl hq :=
      Subtype.ext (direction_lines_unique hed' f.origin_not_mem f.origin_not_mem
        (T.val.direction_spec he (f.planeOrigin hl hq)) hTd (D.right_mem_line _ _) (D.right_mem_line _ _))
    have hT1 := he.eq_one_of_fixed T.val f.origin_not_mem hTo
    exact hT1.symm ▸ Motion.direction_one d

/-- Translations parallel to a fixed affine direction form a subgroup. -/
@[expose] def directionTranslations (d : f.Direction hl hq) : Subgroup (f.translations hl hq) where
  carrier := {T | T.val.HasDirection d}
  one_mem' := Motion.direction_one d
  mul_mem' {T _U} hT hU := hT.mul T.val hU
  inv_mem' {T} hT := hT.inv T.val

/-- Evaluation identifies a direction subgroup with the actual geometric axis. -/
@[expose] def directionTranslationEquiv (d : f.Direction hl hq) :
    f.directionTranslations hl hq d ≃ f.AxisAt d :=
  Equiv.ofBijective (fun T => ⟨(f.translationEquiv hl hq T.val).val,
    (f.translation_direction_iff hl hq T.val d).mp T.property⟩) (by
    constructor
    · intro T U he
      apply Subtype.ext
      apply (f.translationEquiv hl hq).injective
      exact Subtype.ext (congrArg (fun x : f.AxisAt d => x.val) he)
    · intro x
      let b : f.Base hl hq := ⟨x.val,D.line_subset_block d.property.2
        (f.level_spec hl hq f.originPoint).2.2 x.property⟩
      let T := (f.translationEquiv hl hq).symm b
      have hT : T ∈ f.directionTranslations hl hq d := by
        apply (f.translation_direction_iff hl hq T d).mpr
        change (f.translationEquiv hl hq ((f.translationEquiv hl hq).symm b) : Ω) ∈ _
        rw [Equiv.apply_symm_apply]
        exact x.property
      refine ⟨⟨T,hT⟩,?_⟩
      apply Subtype.ext
      exact congrArg (fun x : f.Base hl hq => x.val) ((f.translationEquiv hl hq).apply_symm_apply b))

theorem directionTranslations_card (d : f.Direction hl hq) :
    Nat.card (f.directionTranslations hl hq d) = q := by
  rw [Nat.card_congr (f.directionTranslationEquiv hl hq d)]
  exact f.axisAt_card hl d d.property.1

/-- Every affine line is literally a coset of its direction subgroup in
one and the same regular translation group. -/
theorem affine_line_coset (T U : f.translations hl hq) (d : f.Direction hl hq) :
    (f.translationEquiv hl hq U : Ω) ∈ D.line d (f.translationEquiv hl hq T) ↔
      T⁻¹ * U ∈ f.directionTranslations hl hq d := by
  have hh := (T.val⁻¹).parallel d (T.val.val (f.planeOrigin hl hq))
    (U.val.val (f.planeOrigin hl hq))
  have hcan : (T.val⁻¹).val (T.val.val (f.planeOrigin hl hq)) = f.planeOrigin hl hq := by
    change T.val.val⁻¹ (T.val.val (f.planeOrigin hl hq)) = _
    rw [Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  rw [hcan] at hh
  exact hh.symm.trans (f.translation_direction_iff hl hq (T⁻¹*U) d).symm

/-- The actual affine point set obtains an abelian addition from translations.
This definition is not installed as a global instance. -/
@[expose, instance_reducible] def affineAddCommGroup : AddCommGroup (f.Base hl hq) :=
  ((f.translationEquiv hl hq).symm.trans Additive.ofMul).addCommGroup

section Addition
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq

@[simp] theorem affine_zero : (0 : f.Base hl hq) = f.baseOrigin hl hq := rfl

/-- Translation multiplication is the constructed addition of affine points. -/
theorem translationEquiv_mul (T U : f.translations hl hq) :
    f.translationEquiv hl hq (T*U) = f.translationEquiv hl hq T + f.translationEquiv hl hq U := by
  change _ = f.translationEquiv hl hq
    ((f.translationEquiv hl hq).symm (f.translationEquiv hl hq T) *
      (f.translationEquiv hl hq).symm (f.translationEquiv hl hq U))
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

/-- The affine line through b is exactly b plus the additive axis of its direction. -/
theorem affine_line_add (a b : f.Base hl hq) (d : f.Direction hl hq) :
    (a : Ω) ∈ D.line d b ↔ (a-b : f.Base hl hq).val.val ∈ D.line d f.origin := by
  let T := (f.translationEquiv hl hq).symm b
  let U := (f.translationEquiv hl hq).symm a
  have hh := (f.affine_line_coset hl hq T U d).trans
    (f.translation_direction_iff hl hq (T⁻¹*U) d)
  have hsub : f.translationEquiv hl hq (T⁻¹*U) = a-b := by
    change _ = f.translationEquiv hl hq (U*T⁻¹)
    rw [mul_comm]
  simpa only [T,U,Equiv.apply_symm_apply,hsub] using hh

end Addition
end Theory.GroupAction.SymplecticRankThree.AffineFrame
