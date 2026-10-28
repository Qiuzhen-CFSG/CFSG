module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Reduction
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.ResidualFixer
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField.NormalTwoQuotient
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField
public import Theory.GroupAction.FixedResidualFixerTransport
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.NineExtension.Automorphisms
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.Centerless
public import Theory.SpecificGroups.GL2.ThreeQuaternionUniqueness

/-!
# The marked ternary action of the graph-field centralizer

The monomial calculation identifies the actual embedded two-residual with
`ProjectiveFixer.model`. Every automorphism commuting with graph-field therefore
preserves this subgroup. Transporting its action through an explicit E₉
isomorphism gives a homomorphism from the full centralizer into GL₂(3).

The pointwise-fixer calculation identifies its kernel. The concrete quaternion
subgroup acts faithfully, so its image consists of precisely the eight quaternion
matrices. Matching such a matrix with this inner action leaves an element in the
pointwise fixer, proving membership in the actual inner image joined with
powers of graph-field. No quaternion-placement hypothesis is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(5),
printed p.1171, and the quaternion placement in 16.4.9(2), printed p.1192.
-/

@[expose] public section

namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.GraphField
open Subgroup ExtendedCentralizer ProjectiveFixer
noncomputable section

/-- The actual embedded two-residual is the displayed diagonal-and-cycle E₉. -/
theorem residual_eq_model : projectiveGraphFieldResidual = model := by
  apply le_antisymm _ model_le_projectiveResidual
  change (pResidual 2 ProjectiveGraphField.projectiveAction.fixedSubgroup).map _ ≤ _
  rw [ProjectiveGraphField.projective_residual_eq_of_two_quotient
    ProjectiveGraphField.unitary_quotient_isTwoGroup]
  rw [ProjectiveGraphField.projectiveHeisenberg, Subgroup.map_map,
    ProjectiveGraphField.heisenberg, MonoidHom.map_closure]
  apply (closure_le _).mpr
  rintro _ ⟨x, (rfl | rfl), rfl⟩
  · let u : Fˣ := Units.mk0 ProjectiveGraphField.omega ProjectiveGraphField.omega_ne_zero
    have he : ProjectiveGraphField.diagonalSL = ProjectiveFixer.diagonalSL u := by
      apply Subtype.ext
      have hi : (↑u⁻¹ : F) = ProjectiveGraphField.omega ^ 2 :=
        congrArg Units.val (unit_inv u)
      change Matrix.diagonal ![1, ProjectiveGraphField.omega, ProjectiveGraphField.omega ^ 2] =
        !![1,0,0;0,(u : F),0;0,0,(↑u⁻¹ : F)]
      rw [hi]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u]
    change project ProjectiveGraphField.diagonalSL ∈ model
    rw [he]
    exact diagonal_mem_model u
  · exact cycle_mem_model

/-- Coordinates for the marked subgroup, through its actual injective product embedding. -/
def modelEquiv : model ≃* Multiplicative (Fin 2 → ZMod 3) := by
  let e₁ : Fˣ ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq (p := 3)
    (by rw [Nat.card_units, card_F]) (by simp [Nat.card_eq_fintype_card])
  let e₂ : zpowers cycle ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq (p := 3)
    (by rw [Nat.card_zpowers, cycle_order]) (by simp [Nat.card_eq_fintype_card])
  let e₃ : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) ≃*
      Multiplicative (Fin 2 → ZMod 3) :=
    { toFun := fun x => Multiplicative.ofAdd ![x.1.toAdd, x.2.toAdd]
      invFun := fun x => (Multiplicative.ofAdd (x.toAdd 0), Multiplicative.ofAdd (x.toAdd 1))
      left_inv := by intro x; rfl
      right_inv := by intro x; apply congrArg Multiplicative.ofAdd; ext i; fin_cases i <;> rfl
      map_mul' := by intro x y; apply congrArg Multiplicative.ofAdd; ext i; fin_cases i <;> rfl }
  exact (MonoidHom.ofInjective embedding_injective).symm.trans ((e₁.prodCongr e₂).trans e₃)

/-- Every member of the full centralizer preserves the marked E₉. -/
theorem model_map (x : automorphismCentralizer graphField) :
    model.map x.val.toMonoidHom = model := by
  have he : MulAut.congr x.val graphField = graphField := by
    ext y
    have hc := congrArg (fun a : MulAut PSL => a (x.val.symm y))
      (mem_centralizer_singleton_iff.mp x.property)
    rw [MulAut.congr_apply]
    change x.val (graphField (x.val.symm y)) = graphField y
    simpa only [MulAut.mul_apply, MulEquiv.apply_symm_apply] using hc
  rw [← residual_eq_model]
  exact (MulAut.map_embeddedFixedResidual 2 x.val graphField).trans (congrArg _ he)

/-- Restriction of the actual ambient automorphisms to the marked subgroup. -/
def modelAction : automorphismCentralizer graphField →* MulAut model where
  toFun x := (x.val.subgroupMap model).trans (MulEquiv.subgroupCongr (model_map x))
  map_one' := by ext y; rfl
  map_mul' _ _ := by ext y; rfl

/-- Compatibility with the action on the projective matrix group. -/
theorem modelAction_apply (x : automorphismCentralizer graphField) (y : model) :
    (modelAction x y : PSL) = x.val y.val := rfl

/-- The induced ternary matrix action of the full graph-field centralizer. -/
def matrixAction : automorphismCentralizer graphField →* GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (NineExtension.automorphismEquiv.toMonoidHom.comp (MulAut.congr modelEquiv).toMonoidHom).comp modelAction

/-- Its kernel is exactly the computed pointwise fixer. -/
theorem matrixAction_eq_one_iff (x : automorphismCentralizer graphField) :
    matrixAction x = 1 ↔ x.val ∈ candidate := by
  have he : matrixAction x = 1 ↔ modelAction x = 1 := by
    exact (((MulAut.congr modelEquiv).trans NineExtension.automorphismEquiv).map_eq_one_iff)
  rw [he, ← model_fixer_eq_candidate]
  constructor
  · intro h
    refine ⟨by rw [standard_eq_top]; trivial, ?_⟩
    intro y
    exact congrArg Subtype.val (congrArg (fun a : MulAut model => a y) h)
  · intro h
    ext y
    exact h.2 y

/-- The concrete quaternion subgroup acts by actual inner automorphisms. -/
def quaternionConj : Centerless.quaternion →* automorphismCentralizer graphField :=
  (MulAut.conj.comp Centerless.quaternion.subtype).codRestrict _ (by
    intro q
    apply mem_centralizer_singleton_iff.mpr
    ext y
    have hq : graphField (q : PSL) = q :=
      (MulAut.mem_fixedSubgroup _ _).mp (Centerless.quaternion_le_fixed q.property)
    change (q : PSL) * graphField y * (q : PSL)⁻¹ = graphField ((q : PSL) * y * (q : PSL)⁻¹)
    rw [map_mul, map_mul, map_inv, hq])

/-- Its restriction to E₉, expressed in ternary coordinates. -/
def quaternionMatrix : Centerless.quaternion →* GeneralLinearGroup (Fin 2) (ZMod 3) :=
  matrixAction.comp quaternionConj

/-- Faithfulness follows from its trivial intersection with the centralizer of E₉. -/
theorem quaternionMatrix_injective : Function.Injective quaternionMatrix := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro q hq
  have hc := candidate_fixes_model ((matrixAction_eq_one_iff (quaternionConj q)).mp hq)
  have hcentral : (q : PSL) ∈ centralizer (model : Set PSL) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have he := congrArg (fun z : PSL => z * (q : PSL)) (hc ⟨y, hy⟩)
    change (q : PSL) * y * (q : PSL)⁻¹ * (q : PSL) = y * (q : PSL) at he
    simpa only [inv_mul_cancel_right] using he.symm
  have hb : (q : PSL) ∈ Centerless.quaternion ⊓ centralizer (model : Set PSL) :=
    ⟨q.property, hcentral⟩
  rw [Centerless.quaternion_inf_centralizer_model] at hb
  exact Subtype.ext (mem_bot.mp hb)

/-- Every element of the pointwise fixer is inner times a power of graph-field. -/
theorem candidate_le_innerWith : candidate ≤ innerWith graphField := by
  rintro x ⟨⟨y,t⟩, rfl⟩
  exact (innerWith graphField).mul_mem (mem_sup_left ⟨(y : PSL), rfl⟩)
    (mem_sup_right (npow_mem_zpowers graphField t.toAdd.val))

/-- All eight quaternion matrix fibers lie in the actual inner image joined with graph-field. -/
theorem quaternion_fibers_inner (x : automorphismCentralizer graphField)
    (hx : (matrixAction x).val = 1 ∨ (matrixAction x).val = -1 ∨
      (matrixAction x).val ^ 2 = -1) : x.val ∈ innerWith graphField := by
  have he : Nonempty (quaternionMatrix.range ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := Centerless.quaternion_equiv
    exact ⟨(MonoidHom.ofInjective quaternionMatrix_injective).symm.trans e⟩
  obtain ⟨q, hq⟩ := (GeneralLinearGroup.three_mem_quaternion_iff
    quaternionMatrix.range he (matrixAction x)).mpr hx
  have hk : matrixAction (x * (quaternionConj q)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hq]
    exact mul_inv_cancel _
  have hmem := candidate_le_innerWith ((matrixAction_eq_one_iff _).mp hk)
  have hqmem : (quaternionConj q).val ∈ innerWith graphField :=
    mem_sup_left ⟨q.val, rfl⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using
    (innerWith graphField).mul_mem hmem hqmem

/-- The marked involution as an element of its full automorphism centralizer. -/
def markedInvolution : automorphismCentralizer graphField :=
  ⟨graphField, mem_centralizer_singleton_iff.mpr rfl⟩

/-- Conjugation by the marked E₉, valued in the full centralizer. -/
def modelConj : model →* automorphismCentralizer graphField :=
  modelInner.codRestrict _ (fun y =>
    mem_centralizer_singleton_iff.mpr (modelInner_commute_graphField y).eq)

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.GraphField
