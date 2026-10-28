module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# A natural binary representation of Aut(SL₂(F))

For a finite field of characteristic two, inner-field factorization is unique:
traces detect the field automorphism, and SL₂ has trivial center. Consequently
SL₂(F) semidirect Aut(F) is the actual automorphism group. Its column action
provides a canonical semilinear extension of the natural module, with the
original inner action and field coefficient retained.

This supplies the single-copy action needed to construct the multiplicity
representation in Aschbacher--Smith D.3.21, printed pp.206--207. The group
factorization uses the existing source proof in PSL2.SemilinearCoverage.
-/

@[expose] public noncomputable section
namespace Representation.SL2AutomorphismNatural
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2
abbrev SL := SpecialLinearGroup (Fin 2) F
abbrev V := Fin 2 → F

/-- Entrywise field automorphisms of the literal special-linear group. -/
def fieldHom : (F ≃+* F) →* MulAut (SL (F := F)) where
  toFun := Theory.PSL2.sl2FieldAut
  map_one' := by ext g i j; rfl
  map_mul' _ _ := by ext g i j; rfl

abbrev Parameters := (SL (F := F)) ⋊[fieldHom] (F ≃+* F)

/-- Inner-field parameters act on the marked SL₂ group. -/
def parameterAut : Parameters (F := F) →* MulAut (SL (F := F)) :=
  SemidirectProduct.lift MulAut.conj fieldHom (by
    intro σ
    ext g x
    simp [MulAut.conj_apply])

/-- Inner-field factorization is unique, including over the field of two elements. -/
theorem parameterAut_bijective : Function.Bijective (parameterAut (F := F)) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    intro a ha
    have hh : MulAut.conj a.left * Theory.PSL2.sl2FieldAut a.right = 1 := ha
    have hs : a.right = 1 := Theory.PSL2.sl2FieldAut_eq_conj_implies_refl a.right a.left⁻¹
      (by simpa only [map_inv] using eq_inv_of_mul_eq_one_right hh)
    have hf : Theory.PSL2.sl2FieldAut a.right = 1 := by
      change fieldHom a.right = 1
      rw [hs,map_one]
    rw [hf,mul_one] at hh
    have hc : a.left ∈ Subgroup.center (SL (F := F)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := DFunLike.congr_fun hh g
      change a.left * g * a.left⁻¹ = g at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [Theory.PSL2.sl2_center_eq_bot F] at hc
    exact SemidirectProduct.ext (Subgroup.mem_bot.mp hc) hs
  · intro a
    obtain ⟨g,σ,ha⟩ := Theory.PSL2.sl2_semilinear_coverage a
    exact ⟨⟨g,σ⟩,ha.symm⟩

/-- The actual automorphism group, with its compatible inner-field marking. -/
def parameterEquiv : Parameters (F := F) ≃* MulAut (SL (F := F)) :=
  MulEquiv.ofBijective parameterAut parameterAut_bijective

def linear : SL (F := F) →* (V (F := F) ≃ₗ[ZMod 2] V (F := F)) where
  toFun g := (SpecialLinearGroup.toLin' g).restrictScalars (ZMod 2)
  map_one' := by ext v i; exact congrFun (LinearEquiv.congr_fun SpecialLinearGroup.toLin'.map_one v) i
  map_mul' g h := by ext v i; exact congrFun (LinearEquiv.congr_fun (SpecialLinearGroup.toLin'.map_mul g h) v) i

def coefficient : (F ≃+* F) →* (V (F := F) ≃ₗ[ZMod 2] V (F := F)) where
  toFun σ := {
    toFun v i := σ (v i)
    invFun v i := σ.symm (v i)
    left_inv v := by ext i; exact σ.symm_apply_apply _
    right_inv v := by ext i; exact σ.apply_symm_apply _
    map_add' v w := by ext i; exact map_add σ _ _
    map_smul' c v := by
      ext i
      fin_cases c
      · change σ ((0 : ZMod 2) • v i) = (0 : ZMod 2) • σ (v i)
        simp
      · change σ ((1 : ZMod 2) • v i) = (1 : ZMod 2) • σ (v i)
        simp }
  map_one' := by ext v i; rfl
  map_mul' _ _ := by ext v i; rfl

def natural : Parameters (F := F) →* (V (F := F) ≃ₗ[ZMod 2] V (F := F)) :=
  SemidirectProduct.lift linear coefficient (by
    intro σ
    ext g v i
    change ((g.val.map σ).mulVec v) i = σ (g.val.mulVec (fun j => σ.symm (v j)) i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul,
      RingEquiv.apply_symm_apply, Matrix.map_apply])

omit [Finite F] in
theorem natural_semilinear (a : Parameters (F := F)) (c : F) (v : V (F := F)) :
    natural a (c • v) = a.right c • natural a v := by
  change a.left.val.mulVec (fun i => a.right (c * v i)) = _
  simp only [map_mul]
  exact Matrix.mulVec_smul a.left.val (a.right c) (fun i => a.right (v i))

omit [Finite F] in
theorem natural_intertwines (a : Parameters (F := F)) (g : SL (F := F)) (v : V (F := F)) :
    natural a (g.val.mulVec v) = (parameterAut a g).val.mulVec (natural a v) := by
  have hfield : (fun i => a.right (g.val.mulVec v i)) =
      (Theory.PSL2.sl2FieldAut a.right g).val.mulVec (fun i => a.right (v i)) := by
    ext i
    simp [Matrix.mulVec,dotProduct,Theory.PSL2.sl2FieldAut]
  change a.left.val.mulVec (fun i => a.right (g.val.mulVec v i)) =
    (a.left * Theory.PSL2.sl2FieldAut a.right g * a.left⁻¹).val.mulVec
      (a.left.val.mulVec (fun i => a.right (v i)))
  rw [hfield]
  symm
  rw [Matrix.mulVec_mulVec]
  change ((a.left * Theory.PSL2.sl2FieldAut a.right g * a.left⁻¹) * a.left).val.mulVec _ = _
  rw [mul_assoc (a.left * _),inv_mul_cancel,mul_one]
  exact (Matrix.mulVec_mulVec _ _ _).symm

/-- The canonical binary natural action of the full abstract automorphism group. -/
def action : Representation (ZMod 2) (MulAut (SL (F := F))) (V (F := F)) :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp natural).comp parameterEquiv.symm.toMonoidHom

/-- The field coefficient of the same canonical action. -/
def fieldAction : MulAut (SL (F := F)) →* (F ≃+* F) :=
  SemidirectProduct.rightHom.comp parameterEquiv.symm.toMonoidHom

theorem action_semilinear (a : MulAut (SL (F := F))) (c : F) (v : V (F := F)) :
    action a (c • v) = fieldAction a c • action a v :=
  natural_semilinear _ c v

theorem action_intertwines (a : MulAut (SL (F := F))) (g : SL (F := F)) (v : V (F := F)) :
    action a (g.val.mulVec v) = (a g).val.mulVec (action a v) := by
  have h := natural_intertwines (parameterEquiv.symm a) g v
  have he : parameterAut (parameterEquiv.symm a) = a := parameterEquiv.apply_symm_apply a
  rwa [he] at h

theorem action_conj (g : SL (F := F)) (v : V (F := F)) :
    action (MulAut.conj g) v = g.val.mulVec v := by
  have he : parameterEquiv (SemidirectProduct.inl g) = MulAut.conj g := by
    change parameterAut (SemidirectProduct.inl g) = _
    exact SemidirectProduct.lift_inl _ _ _ _
  change natural (parameterEquiv.symm (MulAut.conj g)) v = _
  rw [←he,parameterEquiv.symm_apply_apply]
  rfl
omit [Finite F] [CharP F 2] in
/-- Covariance on two natural copies determines an inner component actor when
its operator on those copies is diagonal. This retains the same matrix marking. -/
theorem automorphism_eq_conj_of_diagonal
    (a : MulAut (SL (F := F))) (g : SL (F := F))
    (h : ∀ (d : SL (F := F)) (x : Fin 2 → V (F := F)),
      (fun i => g.val.mulVec (d.val.mulVec (x i))) =
        (fun i => (a d).val.mulVec (g.val.mulVec (x i)))) :
    a = MulAut.conj g := by
  apply MulEquiv.ext
  intro d
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have hh := congrFun (h d (fun _ => (g⁻¹).val.mulVec v)) 0
  have hg : g.val.mulVec ((g⁻¹).val.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec]
    change (g * g⁻¹).val.mulVec v = v
    simp
  rw [hg] at hh
  change (a d).val.mulVec v = (g*d*g⁻¹).val.mulVec v
  change (a d).val.mulVec v = ((g.val * d.val) * (g⁻¹).val).mulVec v
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  exact hh.symm

end Representation.SL2AutomorphismNatural
