module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.CentralFactorKernel
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FullAction
/-!
# The full square action with a central factor

A nontrivial action of a two-perfect subgroup has image divisible by three,
because the kernel of the square action is a two-group. Noncommuting images
in one common two-subgroup generate a Sylow two-subgroup of O4+(2). Its
maximality forces the full order-72 action. The criterion retains the actual
two-subgroup containing both elements in the source movement step.

Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/

@[expose] public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {P D E F : Type*} [Group P] [Finite P] [Group D] [Finite D]
  [IsElementaryAbelian 2 D] [Group E] [Group F]
  (d : QuaternionCentralProductData P) (e : E ≃* P × D)

/-- The source's two-perfect action and noncommuting common two-subgroup
force the entire order-72 square action. -/
theorem centralFactorWreathAction_range_eq_top
    (hD : Nat.card D ≤ 2) (f : F →* MulAut E)
    (K T : Subgroup F) (hK : IsPPerfect 2 K) (hT : IsPGroup 2 T)
    (hne : f.comp K.subtype ≠ 1) (x u : T)
    (hmove : d.centralFactorWreathAction e (f x) * d.centralFactorWreathAction e (f u) ≠
      d.centralFactorWreathAction e (f u) * d.centralFactorWreathAction e (f x)) :
    ((d.centralFactorWreathAction e).comp f).range = ⊤ := by
  let g := (d.centralFactorWreathAction e).comp f
  let A := T.map g
  have h3K : 3 ∣ Nat.card (g.comp K.subtype).range :=
    d.three_dvd_centralFactorWreathAction_range e hD hK (f.comp K.subtype) hne
  have hleK : (g.comp K.subtype).range ≤ g.range := by
    rintro y ⟨k,rfl⟩
    exact ⟨k,rfl⟩
  have h3 : 3 ∣ Nat.card g.range := h3K.trans (card_dvd_of_le hleK)
  have hAJ : A ≤ g.range := by
    rintro y ⟨t,_,rfl⟩
    exact ⟨t,rfl⟩
  have hx : g x ∈ A := mem_map_of_mem g x.property
  have hu : g u ∈ A := mem_map_of_mem g u.property
  exact BinaryFourPlus.eq_top_of_three_dvd_of_noncommuting_two_subgroup g.range A hAJ
    (hT.map g) h3 ⟨g x,hx⟩ ⟨g u,hu⟩ (fun hh => hmove (congrArg Subtype.val hh))

end Subgroup.QuaternionCentralProductData
