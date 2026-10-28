module
public import Theory.Representation.SL3.NaturalDualOddDisplacement

/-!
# Binary coordinates for the covered natural and twisted pair

The second binary constituent is identified with the literal field dual,
with the same original full SL₃ actor. No field-linearity of these binary
coordinates is assumed. Rank stays on the actual covering group.
Source: Aschbacher--Smith H.4.1, printed pp.377--379.
-/
public noncomputable section
open Matrix Module Subgroup Representation.BinaryOffender
namespace Representation.SL3NaturalFixed
variable {F H K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group H] [Group K] [Finite K]

/-- Transfer the covered beta bound through the literal second binary coordinates. -/
theorem twisted_pair_odd_displacement_of_cover
    (a : MulAut (SpecialLinearGroup (Fin 3) F))
    (d : (Fin 3 → F) ≃ₗ[ZMod 2] Module.Dual F (Fin 3 → F))
    (hd : ∀ g v, d (specialLinearNatural 3 (a g) v) =
      (specialLinearNatural 3).dual g (d v))
    (β γ : Representation (ZMod 2) H (Fin 3 → F))
    (hfaithful : Function.Injective (β.prod γ))
    (α : H →* MulAut (SpecialLinearGroup (Fin 3) F))
    (hβ : ∀ x g v, β x (specialLinearNatural 3 g v) =
      specialLinearNatural 3 (α x g) (β x v))
    (hγ : ∀ x g v, γ x (specialLinearNatural 3 (a g) v) =
      specialLinearNatural 3 (a (α x g)) (γ x v))
    (f : K →* H) (hfs : Function.Surjective f)
    (j : SpecialLinearGroup (Fin 3) F →* H)
    (hjβ : ∀ g v, β (j g) v = specialLinearNatural 3 g v)
    (hjγ : ∀ g v, γ (j g) v = specialLinearNatural 3 (a g) v)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hrank : primeRank p K ≤ 2)
    (x : H) (hx : orderOf x=p) :
    4*finrank (ZMod 2) F ≤ fixedCodim (β.prod γ) (zpowers x) := by
  let δ : Representation (ZMod 2) H (Module.Dual F (Fin 3 → F)) :=
    d.conjRingEquiv.toMonoidHom.comp γ
  have hδ (y : H) (g) (φ : Module.Dual F (Fin 3 → F)) :
      δ y ((specialLinearNatural 3).dual g φ)=
        (specialLinearNatural 3).dual (α y g) (δ y φ) := by
    obtain ⟨v,rfl⟩ := d.surjective φ
    change d (γ y (d.symm ((specialLinearNatural 3).dual g (d v)))) =
      (specialLinearNatural 3).dual (α y g) (d (γ y (d.symm (d v))))
    rw [←hd,d.symm_apply_apply,d.symm_apply_apply,hγ,hd]
  let C := (LinearEquiv.refl (ZMod 2) (Fin 3 → F)).prodCongr d
  have hcoord (y : H) (v : (Fin 3 → F) × (Fin 3 → F)) :
      C ((β.prod γ) y v)=(β.prod δ) y (C v) := by
    refine Prod.ext ?_ ?_
    · rfl
    change d (γ y v.2)=d (γ y (d.symm (d v.2)))
    rw [d.symm_apply_apply]
  have hfid : Function.Injective (β.prod δ) := by
    intro y z heq
    apply hfaithful
    apply LinearMap.ext
    intro v
    apply C.injective
    rw [hcoord,hcoord,heq]
  have hjδ (g) (φ : Module.Dual F (Fin 3 → F)) :
      δ (j g) φ=(specialLinearNatural 3).dual g φ := by
    obtain ⟨v,rfl⟩ := d.surjective φ
    change d (γ (j g) (d.symm (d v)))=(specialLinearNatural 3).dual g (d v)
    rw [d.symm_apply_apply,hjγ,hd]
  have hbnd := natural_dual_odd_displacement_of_cover β δ hfid α hβ hδ f hfs j
    hjβ hjδ hp hodd hrank x hx
  have hc := fixedCodim_map_equivariant (β.prod γ) (β.prod δ) (MonoidHom.id H) C hcoord (zpowers x)
  simp only [Subgroup.map_id] at hc
  rwa [←hc] at hbnd
end Representation.SL3NaturalFixed
