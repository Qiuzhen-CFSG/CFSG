module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.CubicFixed
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Solvable

/-!
# The actual radical fixed by the marked cubic

The Hermitian parametrization counts the whole fixed subgroup inside the
literal plane radical. An embedded subgroup of the same order centralized
by the marked cubic is therefore that entire fixed subgroup. It contains
the explicit conjugate of the marked long root. Any group centralizing
it embeds in a conjugate of the long-root centralizer.

This supplies the final fixed-four obstruction in Aschbacher–Smith
F.4.42, printed pp.295–296, without identifying the cubic fixed subgroup
with the smaller subgroup fixed by the full S₃.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "L" => localFactor F (form F σ hσ)
local notation "Q" => radical F σ hσ

/-- Fixed elements of the actual plane radical under the cubic Levi element. -/
def fixedRadical : Subgroup Q :=
  (MulAut.conjNormal (H := Q) (levi F σ hσ (cubic F))).fixedSubgroup

/-- Every fixed element has one and only one field parameter. -/
def fixedRadicalEquiv : fixedRadical F σ hσ ≃ F where
  toFun u := ((radicalEquiv F σ hσ).symm u.val).toAdd.val 0 1
  invFun b := ⟨radicalEquiv F σ hσ (Multiplicative.ofAdd (fixedParameter F σ hσ b)), by
    rw [fixedRadical, MulAut.mem_fixedSubgroup]
    rw [radicalEquiv_conj, factorRestriction_levi, toAdd_ofAdd,
      fixedParameter_fixed]⟩
  left_inv u := by
    apply Subtype.ext
    let X := ((radicalEquiv F σ hσ).symm u.val).toAdd
    have hu0 : radicalEquiv F σ hσ (Multiplicative.ofAdd X) = u.val := by
      simp [X]
    have hu : MulAut.conjNormal (levi F σ hσ (cubic F))
        (radicalEquiv F σ hσ (Multiplicative.ofAdd X)) =
          radicalEquiv F σ hσ (Multiplicative.ofAdd X) := by
      rw [hu0]
      exact (MulAut.mem_fixedSubgroup _ _).mp u.property
    rw [radicalEquiv_conj, factorRestriction_levi] at hu
    have hx : hermitianCongruence F σ hσ (cubic F) X = X :=
      congrArg Multiplicative.toAdd ((radicalEquiv F σ hσ).injective hu)
    have he := (cubic_fixed_iff F σ hσ X).mp hx
    change radicalEquiv F σ hσ
      (Multiplicative.ofAdd (fixedParameter F σ hσ (X.val 0 1))) = u.val
    rw [← he]
    exact (radicalEquiv F σ hσ).apply_symm_apply u.val
  right_inv b := by
    simp only [MulEquiv.symm_apply_apply]
    rfl

theorem fixedRadical_card : Nat.card (fixedRadical F σ hσ) = Nat.card F :=
  Nat.card_congr (fixedRadicalEquiv F σ hσ)

/-- The marked long-root element in the determinant-one plane local. -/
def longLocal : L :=
  (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))).val

variable {G : Type*} [Group G]
variable (f : localFactor F (form F σ hσ) →* G) (hf : Function.Injective f)

include hf in
/-- A subgroup of the full cubic-fixed order contains a long-root conjugate.
All inclusions and the conjugating element use the original local embedding. -/
theorem fixed_order_subgroup_contains_long_conjugate
    (E : Subgroup G) (hEQ : E ≤ (Q).map f)
    (hEc : E ≤ centralizer ({f (levi F σ hσ (cubic F))} : Set G))
    (hEcard : Nat.card E = Nat.card F)
    (b : F) (ht : b + σ b = 1) (hn : b * σ b = 1) :
    ∃ u ∈ E, f (levi F σ hσ (longConjugator F σ b)) * f (longLocal F σ hσ) *
      (f (levi F σ hσ (longConjugator F σ b)))⁻¹ = u := by
  let j : Q →* G := f.comp (Q).subtype
  have hj : Function.Injective j := hf.comp (Q).subtype_injective
  let W := (fixedRadical F σ hσ).map j
  let : Finite W := Finite.of_surjective (j.subgroupMap (fixedRadical F σ hσ))
    (j.subgroupMap_surjective _)
  have hEW : E ≤ W := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hEQ hx
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    apply hf
    change f (levi F σ hσ (cubic F) * y * (levi F σ hσ (cubic F))⁻¹) = f y
    rw [map_mul, map_mul, map_inv]
    have hc := mem_centralizer_singleton_iff.mp (hEc hx)
    rw [← hc]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hWcard : Nat.card W = Nat.card F := by
    rw [← Nat.card_congr ((fixedRadical F σ hσ).equivMapOfInjective j hj).toEquiv,
      fixedRadical_card]
  have hEW' : E = W := eq_of_le_of_card_ge hEW (by rw [hWcard, hEcard])
  let v : Q := radicalEquiv F σ hσ (Multiplicative.ofAdd (fixedParameter F σ hσ b))
  have hv : v ∈ fixedRadical F σ hσ := by
    rw [fixedRadical, MulAut.mem_fixedSubgroup]
    dsimp only [v]
    rw [radicalEquiv_conj, factorRestriction_levi, toAdd_ofAdd,
      fixedParameter_fixed]
  refine ⟨j v, hEW' ▸ (show j v ∈ W from ⟨v, hv, rfl⟩), ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg f
  apply Subtype.ext
  exact long_unipotent_conjugation F σ hσ b ht hn

include hf in
/-- The centralizer of such a fixed subgroup is solvable whenever the
marked long-root centralizer is solvable. -/
theorem centralizing_fixed_order_subgroup_isSolvable
    (E : Subgroup G) (hEQ : E ≤ (Q).map f)
    (hEc : E ≤ centralizer ({f (levi F σ hσ (cubic F))} : Set G))
    (hEcard : Nat.card E = Nat.card F)
    (b : F) (ht : b + σ b = 1) (hn : b * σ b = 1)
    (hz : Group.IsSolvable (centralizer ({f (longLocal F σ hσ)} : Set G)))
    (A : Subgroup G) (hA : A ≤ centralizer (E : Set G)) : Group.IsSolvable A := by
  obtain ⟨u, hu, he⟩ := fixed_order_subgroup_contains_long_conjugate F σ hσ f hf
    E hEQ hEc hEcard b ht hn
  let a := f (levi F σ hσ (longConjugator F σ b))
  let e := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
    (MulAut.conj a) (f (longLocal F σ hσ))
  have heu : MulAut.conj a (f (longLocal F σ hσ)) = u := he
  have hsol : Group.IsSolvable (centralizer ({u} : Set G)) := by
    rw [← heu]
    let := hz
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let := hsol
  have hAu : A ≤ centralizer ({u} : Set G) :=
    hA.trans (centralizer_le (Set.singleton_subset_iff.mpr hu))
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion hAu) (inclusion_injective hAu)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
