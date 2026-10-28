module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.Action
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.SL2NaturalOffenders.Internal

/-!
# The starred two-group lies in the actual SL₂ layer

The faithful natural action of LT* restricts to a binary representation.
Normality of its SL₂ layer supplies semilinearity. Since U* fixes the entire
nonzero marked field line pointwise, the scalar automorphism is trivial.
G.2.2 makes U* elementary, so each resulting linear transformation has
square one and determinant one in characteristic two. Faithfulness then
places that same actor in the supplied L*, without an innerness assumption.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3(1), printed p.333, PDF p.344.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F] {n : ℕ} {g : G}
  (d : Hypothesis D F n g)
include d

theorem field_char_two : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by
    simpa only [← Nat.card_eq_fintype_card] using d.field_card)

section Binary
variable [Algebra (ZMod 2) F]

/-- Restriction of scalars of the actual starred natural action. -/
noncomputable def binaryRepresentation : Representation (ZMod 2) D.Star (Fin 2 → F) where
  toFun x := (AddMonoidHom.toMultiplicative.symm
    (d.coordinateAction x).toMonoidHom).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change (d.coordinateAction 1 (Multiplicative.ofAdd v)).toAdd = v
    rw [map_one]
    rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro v
    change (d.coordinateAction (x * y) (Multiplicative.ofAdd v)).toAdd =
      (d.coordinateAction x (d.coordinateAction y (Multiplicative.ofAdd v))).toAdd
    rw [map_mul]
    rfl

theorem binaryRepresentation_apply (x : D.Star) (v : Fin 2 → F) :
    d.binaryRepresentation x v = (d.coordinateAction x (Multiplicative.ofAdd v)).toAdd := rfl

theorem binaryRepresentation_injective : Function.Injective d.binaryRepresentation := by
  intro x y he
  apply d.coordinateAction_injective
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  exact LinearMap.congr_fun he v.toAdd

theorem binaryRepresentation_on_L (l : D.star D.L) (v : Fin 2 → F) :
    d.binaryRepresentation (l : D.Star) v = (d.model l).val *ᵥ v := by
  rw [binaryRepresentation_apply, d.coordinateAction_on_L]
  rfl

/-- A pointwise-fixed nonzero field line kills the scalar automorphism
supplied by normality of the natural SL₂ layer. -/
theorem star_U_linear (u : D.star D.U) (c : F) (v : Fin 2 → F) :
    d.binaryRepresentation (u : D.Star) (c • v) =
      c • d.binaryRepresentation (u : D.Star) v := by
  let : (D.star D.L).Normal := d.star_L_normal
  obtain ⟨σ, hσ⟩ := Representation.SL2NaturalOffenders.normalizer_semilinear
    (D.star D.L) d.model d.binaryRepresentation d.binaryRepresentation_on_L (u : D.Star)
  have hp : d.point ≠ ⊥ := by
    intro he
    have hdim := d.point_dimension
    rw [he, finrank_bot] at hdim
    exact Nat.zero_ne_one hdim
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hfix (z : Fin 2 → F) (hz : z ∈ d.point) :
      d.binaryRepresentation (u : D.Star) z = z :=
    congrArg Multiplicative.toAdd (d.coordinateAction_U_fixes_point u z hz)
  have hc : σ c = c := by
    have he := hσ c w
    rw [hfix _ (d.point.smul_mem c hw), hfix w hw] at he
    exact (smul_left_injective F hw0) he.symm
  rw [hσ, hc]

end Binary

/-- The actual U* lies in L*. No G.2.3 conclusion is a premise:
G.2.2 supplies the elementary image, and pointwise line fixation supplies
linearity, so the faithful matrix action identifies each actor in SL₂. -/
theorem star_U_le_star_L (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : D.star D.U ≤ D.star D.L := by
  let : CharP F 2 := d.field_char_two
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hel := d.star_U_elementary hUT hf
  intro u hu
  have hs : u ^ 2 = 1 := by
    have he := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p)
      (⟨u, hu⟩ : D.star D.U)
    exact congrArg Subtype.val he
  exact Representation.SL2NaturalOffenders.mem_of_linear_square_one
    (D.star D.L) d.model d.binaryRepresentation d.binaryRepresentation_injective
    d.binaryRepresentation_on_L hs (d.star_U_linear ⟨u, hu⟩)

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
