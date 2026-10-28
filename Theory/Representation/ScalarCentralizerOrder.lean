module
public import Theory.Representation.NaturalCommutantOrder

/-!
# Scalar commutants bound the original relative centralizer

The actual faithful action embeds the relative centralizer in the full
additive automorphism commutant. If the latter consists of field scalars,
its order divides q-1. No splitting or absolute irreducibility is assumed.
This supplies the centralizer factor in natural-automizer index bounds.
Source application: Aschbacher--Smith 11.2.1, printed pp.766--767.
-/

public noncomputable section
open Subgroup
namespace Representation
variable {F H W : Type*} [Field F] [Finite F] [Group H]
  [AddCommGroup W] [Module (ZMod 2) W] [Module F W] [Nontrivial W]

/-- A faithful scalar-commutant action bounds the original relative centralizer. -/
theorem centralizer_card_dvd_of_scalar_commutant
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ) (K : Subgroup H)
    (hs : ∀ f : W →+ W, (∀ g : K, ∀ v, f (ρ g v) = ρ g (f v)) →
      ∃ c : F, ∀ v, f v = c • v) :
    Nat.card (centralizer (K : Set H)) ∣ Nat.card F - 1 := by
  let a : H →* MulAut (Multiplicative W) :=
    { toFun h := AddEquiv.toMultiplicative
        (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom h)).toAddEquiv
      map_one' := by ext v; exact LinearMap.congr_fun ρ.map_one v.toAdd
      map_mul' g h := by ext v; exact LinearMap.congr_fun (ρ.map_mul g h) v.toAdd }
  have ha : Function.Injective a := by
    intro g h he
    apply hρ
    apply LinearMap.ext
    intro v
    exact congrArg (fun t : MulAut (Multiplicative W) => (t (Multiplicative.ofAdd v)).toAdd) he
  let f := a.comp K.subtype
  have hc := Theory.GroupTheory.commutant_card_dvd_scalars f (MulEquiv.refl (Multiplicative W))
    (F := F) (V := W) (by
      intro c hc
      let b : W →+ W := (AddEquiv.toMultiplicative.symm c).toAddMonoidHom
      apply hs b
      intro g v
      exact (congrArg (fun t : MulAut (Multiplicative W) =>
        (t (Multiplicative.ofAdd v)).toAdd) (hc (f g) ⟨g,rfl⟩)).symm)
  have hmap : (centralizer (K : Set H)).map a ≤ centralizer (f.range : Set _) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨g,rfl⟩
    change a g * a x = a x * a g
    rw [← map_mul, ← map_mul, hx g g.property]
  have hd := (card_dvd_of_le hmap).trans hc
  rwa [card_map_of_injective ha] at hd

end Representation
