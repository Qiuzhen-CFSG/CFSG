/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayPuncture

/-!
# GolayPunctureAutomorphisms

The automorphism group of the punctured Golay code is multiplicatively equivalent to the
coordinate stabilizer in the extended code. Restriction and extension fixing the deleted
point are inverse, with parity ensuring preservation of the extended code.

Source: `Atlas/Codes/GolayPunctureAutomorphisms.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators
local instance (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem golay_mem_iff_puncture_parity (a : Omega) (w : BinaryWord) :
    w ∈ golay ↔ puncture a w ∈ puncturedGolay a ∧ ∑ x, w x = 0 := by
  constructor
  · intro hw
    refine ⟨⟨w,hw,rfl⟩,?_⟩
    exact (even_weight_iff w).mp (even_iff_two_dvd.mpr
      (dvd_trans (by decide : 2 ∣ 4) (golay_doublyEven w hw)))
  · rintro ⟨⟨v,hv,he⟩,hp⟩
    have eq : v = w := by
      funext x
      by_cases hx : x = a
      · subst x
        rw [sum_puncture a] at hp
        have hs : (∑ y : Mathieu23Points a, v y.val) = ∑ y : Mathieu23Points a, w y.val :=
          Finset.sum_congr rfl (fun y _ => congrFun he y)
        have hpv := golay_parity_recovery a ⟨v,hv⟩
        have hb : ∀ x y : Bit, x + y = 0 → y = x := by decide
        exact hpv.trans (hs.trans (hb _ _ hp))
      · exact congrFun he ⟨x,hx⟩
    exact eq ▸ hv

def puncturedCoordinatePermutation (a : Omega) (σ : Equiv.Perm (Mathieu23Points a)) :
    PuncturedWord a ≃ₗ[Bit] PuncturedWord a where
  toFun w x := w (σ⁻¹ x)
  invFun w x := w (σ x)
  left_inv := by intro w; funext x; simp
  right_inv := by intro w; funext x; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def puncturedCodeAutomorphisms (a : Omega) : Subgroup (Equiv.Perm (Mathieu23Points a)) where
  carrier := {σ | ∀ w, w ∈ puncturedGolay a ↔ puncturedCoordinatePermutation a σ w ∈ puncturedGolay a}
  one_mem' := by intro w; rfl
  mul_mem' := by
    intro σ τ hσ hτ w
    exact (hτ w).trans (hσ _)
  inv_mem' := by
    intro σ hσ w
    have h := hσ (puncturedCoordinatePermutation a σ⁻¹ w)
    have he : puncturedCoordinatePermutation a σ (puncturedCoordinatePermutation a σ⁻¹ w) = w := by
      funext x
      simp [puncturedCoordinatePermutation]
    rw [he] at h
    exact h.symm

def puncturedPermutationExtend (a : Omega) : Equiv.Perm (Mathieu23Points a) →* Equiv.Perm Omega :=
  by
    classical
    exact Equiv.Perm.extendDomainHom (Equiv.refl (Mathieu23Points a))

@[simp] theorem puncturedPermutationExtend_point (a : Omega) (σ : Equiv.Perm (Mathieu23Points a)) :
    puncturedPermutationExtend a σ a = a := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [SubMulAction.mem_ofStabilizer_iff])

@[simp] theorem puncturedPermutationExtend_complement (a : Omega)
    (σ : Equiv.Perm (Mathieu23Points a)) (x : Mathieu23Points a) :
    puncturedPermutationExtend a σ x.val = (σ x).val :=
  by
    classical
    exact Equiv.Perm.extendDomain_apply_image _ _ x

theorem puncture_extend_permutation (a : Omega) (σ : Equiv.Perm (Mathieu23Points a))
    (w : BinaryWord) : puncture a (coordinatePermutation (puncturedPermutationExtend a σ) w) =
      puncturedCoordinatePermutation a σ (puncture a w) := by
  funext x
  change w ((puncturedPermutationExtend a σ)⁻¹ x.val) = w (σ⁻¹ x).val
  rw [← map_inv, puncturedPermutationExtend_complement]

theorem puncturedPermutationExtend_preserving (a : Omega)
    (σ : puncturedCodeAutomorphisms a) : CodePreserving (puncturedPermutationExtend a σ.val) := by
  intro w
  rw [golay_mem_iff_puncture_parity a, golay_mem_iff_puncture_parity a,
    puncture_extend_permutation, ← σ.prop]
  have hs : (∑ x, coordinatePermutation (puncturedPermutationExtend a σ.val) w x) = ∑ x, w x :=
    Equiv.sum_comp (puncturedPermutationExtend a σ.val).symm w
  rw [hs]


def puncturedRestrictionPerm (a : Omega) : Mathieu23PointModel a →* Equiv.Perm (Mathieu23Points a) :=
  MulAction.toPermHom _ _

theorem puncture_restriction_permutation (a : Omega) (g : Mathieu23PointModel a) (w : BinaryWord) :
    puncture a (coordinatePermutation g.val.val w) =
      puncturedCoordinatePermutation a (puncturedRestrictionPerm a g) (puncture a w) := rfl

theorem puncturedRestriction_forward (a : Omega) (g : Mathieu23PointModel a)
    (w : PuncturedWord a) (hw : w ∈ puncturedGolay a) :
    puncturedCoordinatePermutation a (puncturedRestrictionPerm a g) w ∈ puncturedGolay a := by
  obtain ⟨v,hv,rfl⟩ := hw
  exact ⟨coordinatePermutation g.val.val v, (g.val.prop v).mp hv, rfl⟩

def puncturedRestriction (a : Omega) : Mathieu23PointModel a →* puncturedCodeAutomorphisms a where
  toFun g := ⟨puncturedRestrictionPerm a g, fun w => ⟨puncturedRestriction_forward a g w, by
    intro hw
    have h := puncturedRestriction_forward a g⁻¹ _ hw
    have he : puncturedCoordinatePermutation a (puncturedRestrictionPerm a g⁻¹)
        (puncturedCoordinatePermutation a (puncturedRestrictionPerm a g) w) = w := by
      funext x
      simp [puncturedCoordinatePermutation, map_inv]
    rwa [he] at h⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

def puncturedLift (a : Omega) : puncturedCodeAutomorphisms a →* Mathieu23PointModel a where
  toFun σ := ⟨⟨puncturedPermutationExtend a σ.val, puncturedPermutationExtend_preserving a σ⟩,
    puncturedPermutationExtend_point a σ.val⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' σ τ := Subtype.ext (Subtype.ext (map_mul _ σ.val τ.val))

theorem puncturedRestriction_lift (a : Omega) (σ : puncturedCodeAutomorphisms a) :
    puncturedRestriction a (puncturedLift a σ) = σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact puncturedPermutationExtend_complement a σ.val x

theorem puncturedLift_restriction (a : Omega) (g : Mathieu23PointModel a) :
    puncturedLift a (puncturedRestriction a g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x = a
  · subst x
    exact (puncturedPermutationExtend_point a _).trans g.prop.symm
  · exact puncturedPermutationExtend_complement a _ ⟨x,hx⟩

/-- Full automorphism comparison, via restriction and parity extension. -/
def puncturedGolayAutEquiv (a : Omega) : Mathieu23PointModel a ≃* puncturedCodeAutomorphisms a :=
  { puncturedRestriction a with
    invFun := puncturedLift a
    left_inv := puncturedLift_restriction a
    right_inv := puncturedRestriction_lift a }

theorem puncturedGolayAutEquiv_apply (a : Omega) (g : Mathieu23PointModel a)
    (x : Mathieu23Points a) : (puncturedGolayAutEquiv a g).val x = g • x := rfl

end Atlas.Codes
