module
public import Theory.Representation.SL3.PairedOddDisplacement
public import Theory.Representation.SL3.DualLiftCentralizers
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# Covered odd displacement in literal natural and dual coordinates

Inverse transpose identifies the second vector model with the literal field
dual. Both constituents retain the same original full SL₃ action. The rank
hypothesis remains on the actual cover of the paired action.
Source: Aschbacher--Smith H.4.1, printed pp.377--379.
-/
public noncomputable section
open Matrix Module Subgroup Representation.BinaryOffender
namespace Representation.SL3NaturalFixed
variable {F H K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group H] [Group K] [Finite K]

/-- An odd-prime actor on a faithful natural/dual pair moves at least four
field degrees when the actual group covering the paired image has rank two. -/
theorem natural_dual_odd_displacement_of_cover
    (β : Representation (ZMod 2) H (Fin 3 → F))
    (γ : Representation (ZMod 2) H (Module.Dual F (Fin 3 → F)))
    (hfaithful : Function.Injective (β.prod γ))
    (α : H →* MulAut (SpecialLinearGroup (Fin 3) F))
    (hβ : ∀ x g v, β x (specialLinearNatural 3 g v) =
      specialLinearNatural 3 (α x g) (β x v))
    (hγ : ∀ x g φ, γ x ((specialLinearNatural 3).dual g φ) =
      (specialLinearNatural 3).dual (α x g) (γ x φ))
    (f : K →* H) (hfs : Function.Surjective f)
    (j : SpecialLinearGroup (Fin 3) F →* H)
    (hjβ : ∀ g v, β (j g) v = specialLinearNatural 3 g v)
    (hjγ : ∀ g φ, γ (j g) φ = (specialLinearNatural 3).dual g φ)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hrank : primeRank p K ≤ 2)
    (x : H) (hx : orderOf x=p) :
    4*finrank (ZMod 2) F ≤ fixedCodim (β.prod γ) (zpowers x) := by
  let d := SL3ParabolicNatural.dualVectorCoordinates (F := F)
  let a := Matrix.PSL3.OuterSolvable.graphSL F
  have hd (g : SpecialLinearGroup (Fin 3) F) (φ : Module.Dual F (Fin 3 → F)) :
      d ((specialLinearNatural 3).dual g φ)=specialLinearNatural 3 (a g) (d φ) := by
    rw [SL3ParabolicNatural.dualVectorCoordinates_action]
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M *ᵥ d φ)
      (Matrix.adjugate_transpose g.val)
  let db := d.restrictScalars (ZMod 2)
  let δ : Representation (ZMod 2) H (Fin 3 → F) := db.conjRingEquiv.toMonoidHom.comp γ
  have hδ (y : H) (g) (v : Fin 3 → F) :
      δ y (specialLinearNatural 3 (a g) v)=specialLinearNatural 3 (a (α y g)) (δ y v) := by
    obtain ⟨φ,rfl⟩ := d.surjective v
    change d (γ y (d.symm (specialLinearNatural 3 (a g) (d φ)))) =
      specialLinearNatural 3 (a (α y g)) (d (γ y (d.symm (d φ))))
    rw [←hd,d.symm_apply_apply,d.symm_apply_apply,hγ,hd]
  let E := (LinearEquiv.refl (ZMod 2) (Fin 3 → F)).prodCongr db
  have hcoord (y : H) (v : (Fin 3 → F) × Module.Dual F (Fin 3 → F)) :
      E ((β.prod γ) y v)=(β.prod δ) y (E v) := by
    refine Prod.ext ?_ ?_
    · rfl
    change d (γ y v.2)=d (γ y (d.symm (d v.2)))
    rw [d.symm_apply_apply]
  have hfi : Function.Injective (β.prod δ) := by
    intro y z he
    apply hfaithful
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [hcoord,hcoord,he]
  have hcod := fixedCodim_map_equivariant (β.prod γ) (β.prod δ)
    (MonoidHom.id H) E hcoord (zpowers x)
  simp only [Subgroup.map_id] at hcod
  rw [hcod]
  apply paired_odd_displacement_of_cover a d.symm ?_ β δ hfi α hβ hδ f hfs j hjβ ?_
    hp hodd hrank x hx
  · intro g v
    apply d.injective
    rw [d.apply_symm_apply,hd,d.apply_symm_apply]
  · intro g v
    change d (γ (j g) (d.symm v))=specialLinearNatural 3 (a g) v
    rw [hjγ,hd,d.apply_symm_apply]
end Representation.SL3NaturalFixed
