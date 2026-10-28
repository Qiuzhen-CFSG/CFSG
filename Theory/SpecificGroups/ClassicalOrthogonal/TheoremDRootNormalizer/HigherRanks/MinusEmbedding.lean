module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.Coordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
import Mathlib.Tactic

/-!
# Split commutators in the actual minus orthogonal model

When the field has more than two elements, every displayed root is a
commutator with a diagonal scaling. Extending a split isometry by the identity
on the chosen anisotropic plane gives an injective homomorphism into the full
isometry group of `Minus.form`. Restricting to commutators and using the literal
scalar quotient supplies an injective map into `ClassicalGroup.POmegaMinus`.
Together with the squared diagonal commutator in `Coordinates`, this places
the root and all three torus parameters in the exact minus Omega carrier,
including rank four. Source: GLS3 §2.7 and quasithin A.2.18, printed p.40.
-/

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
open scoped commutatorElement
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
variable {F : Type u} [Field F] {r : ℕ}

theorem root_mem_commutator [Finite F] (hq : 2 < Nat.card F)
    {i j : Fin r} (hij : i ≠ j) (a : F) : root hij a ∈ commutator (O r F) := by
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  have hc' : (c : F) - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro h
    exact hc (Units.ext h))
  let d : Fin r → Fˣ := Pi.mulSingle i c
  let b : F := a / ((c : F) - 1)
  have he : ⁅diagonal d, root hij b⁆ = root hij a := by
    rw [commutatorElement_def, diagonal_conj_root]
    have hinv : (root hij b)⁻¹ = root hij (-b) :=
      (map_inv (rootHom hij) (Multiplicative.ofAdd b)).symm
    rw [hinv]
    change rootHom hij (Multiplicative.ofAdd _) *
      rootHom hij (Multiplicative.ofAdd _) = rootHom hij (Multiplicative.ofAdd a)
    rw [← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    change (d i : F) * b * ((d j)⁻¹ : Fˣ) + -b = a
    simp [d, Pi.mulSingle_apply, hij.symm, b]
    field_simp
    ring
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Convert the displayed hyperbolic coordinates of the minus space to the split ordering. -/
def splitCoordinates (x : Minus.Space F r) : VectorD r F :=
  Sum.elim (fun i => (x.1 i).1) (fun i => (x.1 i).2)

def extendLinear (g : O r F) : Minus.Space F r ≃ₗ[F] Minus.Space F r where
  toFun x := (fun i => (g.val (splitCoordinates x) (.inl i),
    g.val (splitCoordinates x) (.inr i)), x.2)
  invFun x := (fun i => (g.val.symm (splitCoordinates x) (.inl i),
    g.val.symm (splitCoordinates x) (.inr i)), x.2)
  left_inv x := by
    have he (v : VectorD r F) : (Sum.elim (fun i => v (.inl i)) (fun i => v (.inr i))) = v := by
      funext k; cases k <;> rfl
    apply Prod.ext
    · funext i
      simp only [splitCoordinates, he, LinearEquiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Prod.mk.eta]
    · rfl
  right_inv x := by
    have he (v : VectorD r F) : (Sum.elim (fun i => v (.inl i)) (fun i => v (.inr i))) = v := by
      funext k; cases k <;> rfl
    apply Prod.ext
    · funext i
      simp only [splitCoordinates, he, LinearEquiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, Prod.mk.eta]
    · rfl
  map_add' x y := by
    have he : splitCoordinates (x+y) = splitCoordinates x + splitCoordinates y := by
      funext k; cases k <;> rfl
    apply Prod.ext
    · funext i; simp [he]
    · rfl
  map_smul' a x := by
    have he : splitCoordinates (a • x) = a • splitCoordinates x := by
      funext k; cases k <;> rfl
    apply Prod.ext
    · funext i; simp [he]
    · rfl

def extend (a : F) (g : O r F) : Minus.Orthogonal F (Minus.Space F r) (Minus.form F r a) :=
  ⟨extendLinear g, (mem_quadraticIsometrySubgroup _ _).mpr (by
    intro x
    simp only [Minus.form_apply]
    change (∑ i, g.val (splitCoordinates x) (.inl i) * g.val (splitCoordinates x) (.inr i)) +
      Minus.plane F a x.2 = _
    have h := (mem_quadraticIsometrySubgroup _ _).mp g.property (splitCoordinates x)
    rw [formD_apply, formD_apply] at h
    rw [h]
    rfl)⟩

@[simp] theorem extend_left (a : F) (g : O r F) (x : Minus.Space F r) (i : Fin r) :
    ((extend a g).val x).1 i =
      (g.val (splitCoordinates x) (.inl i), g.val (splitCoordinates x) (.inr i)) := rfl
@[simp] theorem extend_right (a : F) (g : O r F) (x : Minus.Space F r) :
    ((extend a g).val x).2 = x.2 := rfl
@[simp] theorem splitCoordinates_extend (a : F) (g : O r F) (x : Minus.Space F r) :
    splitCoordinates ((extend a g).val x) = g.val (splitCoordinates x) := by
  funext k
  cases k <;> rfl

def extendHom (a : F) : O r F →* Minus.Orthogonal F (Minus.Space F r) (Minus.form F r a) where
  toFun := extend a
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Prod.ext
    · funext i; simp [splitCoordinates]
    · rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change (extend a (g*h)).val x = (extend a g).val ((extend a h).val x)
    apply Prod.ext
    · funext i; simp
    · rfl

theorem extendHom_injective (a : F) : Function.Injective (extendHom (r := r) a) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  let v : Minus.Space F r := (fun i => (x (.inl i), x (.inr i)), 0)
  have hv : splitCoordinates v = x := by funext k; cases k <;> rfl
  have he := congrArg (fun t : Minus.Orthogonal F (Minus.Space F r) (Minus.form F r a) =>
    splitCoordinates (t.val v)) hgh
  simpa only [extendHom, MonoidHom.coe_mk, OneHom.coe_mk, splitCoordinates_extend, hv] using he

/-- Restrict the actual extension map to commutator groups. -/
def extendOmegaHom (a : F) : commutator (O r F) →*
    Minus.Omega F (Minus.Space F r) (Minus.form F r a) :=
  ((extendHom a).comp (commutator (O r F)).subtype).codRestrict _ (by
    intro g
    have hm : extendHom a g.val ∈ (commutator (O r F)).map (extendHom a) :=
      Subgroup.mem_map_of_mem _ g.property
    rw [map_commutator_eq] at hm
    exact Subgroup.commutator_mono le_top le_top hm)

theorem extendOmegaHom_injective (a : F) : Function.Injective (extendOmegaHom (r := r) a) := by
  intro g h hgh
  apply Subtype.ext
  exact extendHom_injective a (congrArg Subtype.val hgh)

/-- The literal minus projectivization after extension by the anisotropic plane. -/
def minusProjectiveHom [Finite F] [CharP F 2] (r : ℕ) : commutator (O (r-1) F) →*
    ClassicalGroup.POmegaMinus r F :=
  (minusOmegaEquivProjective (F := F) r).toMonoidHom.comp (extendOmegaHom (Minus.parameter F))

theorem minusProjectiveHom_injective [Finite F] [CharP F 2] (r : ℕ) :
    Function.Injective (minusProjectiveHom (F := F) r) :=
  (minusOmegaEquivProjective (F := F) r).injective.comp
    (extendOmegaHom_injective (Minus.parameter F))

end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
