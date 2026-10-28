module

public import Theory.Representation.BinaryCubicEqualFixed
public import Theory.Representation.ElementaryPerfectSplit

/-!
# The cubic fixed-space obstruction on an elementary group

Transport the proved binary operator argument to the literal elementary
abelian group. This retains its automorphisms and element fixed groups,
so no choice of coordinates is required in the original group argument.

Source application: Aschbacher--Smith12.7.19, printed p.846.
-/

public noncomputable section
open scoped IsMulCommutative
namespace MulAut
variable {V : Type*} [Group V] [IsElementaryAbelian 2 V]

/-- Equal element fixed groups force an inverted cubic to be trivial. -/
theorem cubic_eq_one_of_fixed_containment
    (c t s : MulAut V) (hc : c^3=1) (ht : t*t=1)
    (htc : Commute t c) (hsc : s*c=c^2*s)
    (hfix : ∀ v : V, t v=v → s v=v) : c=1 := by
  let σ := Representation.elementaryRepresentation (p := 2) (MonoidHom.id (MulAut V))
  let F : MulAut V →* BinaryLinear.GL (Additive V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)).toMonoidHom.comp
      σ.asGroupHom
  have he (a : MulAut V) (v : Additive V) : F a v=Additive.ofMul (a v.toMul) := rfl
  have hh := BinaryLinear.cubic_eq_one_of_fixed_containment (F c) (F t) (F s)
    (by rw [←map_pow,hc,map_one]) (by rw [←map_mul,ht,map_one])
    (htc.map F) (by rw [←map_mul,←map_pow,←map_mul,hsc]) (by
      intro v hv
      rw [he] at hv ⊢
      exact congrArg Additive.ofMul (hfix v.toMul (congrArg Additive.toMul hv)))
  apply MulEquiv.ext
  intro v
  have hv := congrArg (fun a : BinaryLinear.GL (Additive V) => (a (Additive.ofMul v)).toMul) hh
  exact hv

end MulAut
