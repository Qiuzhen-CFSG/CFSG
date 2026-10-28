module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

/-!
# Binary hyperplane displacement with a fixed seed

If every nonidentity actor moves at least two dimensions, its restriction to
any hyperplane is faithful. When that restriction moves vectors only along a
fixed line and fixes a seed, a dual functional vanishing on the seed records
the actor injectively. Counting the annihilator bounds the acting group.

Source application: the conjugate-center bound in Aschbacher--Smith 12.9.4,
printed pp.859--860. No quadratic form or group classification is needed here.
-/

public noncomputable section
open Module Subgroup
namespace Representation.BinaryHyperplaneDisplacement
variable {A V : Type*} [Group A] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Hyperplane displacement along a line is determined by a functional on
the hyperplane modulo its fixed seed. -/
theorem card_le_of_fixed_seed
    (ρ : Representation (ZMod 2) A V)
    (hlower : ∀ a : A, a ≠ 1 →
      2 ≤ finrank (ZMod 2) (ρ a - LinearMap.id).range)
    (W H : Submodule (ZMod 2) V) (hWH : W ≤ H)
    (hH : finrank (ZMod 2) H + 1 = finrank (ZMod 2) V)
    (v : V) (hv : v ≠ 0)
    (hfix : ∀ a : A, ∀ w ∈ W, ρ a w = w)
    (hmove : ∀ a : A, ∀ w ∈ H, ρ a w - w ∈ Submodule.span (ZMod 2) {v}) :
    Nat.card A ≤ 2 ^ (finrank (ZMod 2) H - finrank (ZMod 2) W) := by
  let W' := W.comap H.subtype
  let D := W'.dualAnnihilator
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  let f (a : A) : Module.Dual (ZMod 2) H :=
    l.comp (((ρ a).comp H.subtype) - H.subtype)
  have heval (a : A) (w : H) : f a w = l (ρ a w - w) := rfl
  have act (a : A) (w : H) : ρ a w = (w:V) + f a w • v := by
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hmove a w w.property)
    have he : f a w = c := by rw [heval,←hc,map_smul,hl,smul_eq_mul,mul_one]
    rw [he,hc,add_sub_cancel]
  have fmem (a : A) : f a ∈ D := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro w hw
    change l (ρ a w - w) = 0
    rw [hfix a w hw,sub_self,map_zero]
  let enc (a : A) : D := ⟨f a,fmem a⟩
  have hinj : Function.Injective enc := by
    intro a b hab
    have he : ∀ w : H, ρ a w = ρ b w := by
      intro w
      have hh := LinearMap.congr_fun (congrArg Subtype.val hab) w
      rw [act a w,act b w,show f a w = f b w from hh]
    have hker : H ≤ (ρ (b⁻¹*a) - LinearMap.id).ker := by
      intro w hw
      change ρ (b⁻¹*a) w - w = 0
      rw [map_mul,Module.End.mul_apply,he ⟨w,hw⟩,Representation.inv_self_apply,sub_self]
    have hr := (ρ (b⁻¹*a) - LinearMap.id).finrank_range_add_finrank_ker
    have hk := Submodule.finrank_mono hker
    have hid : b⁻¹*a = 1 := by
      by_contra hn
      have := hlower (b⁻¹*a) hn
      omega
    exact (inv_mul_eq_one.mp hid).symm
  have hdimW : finrank (ZMod 2) W' = finrank (ZMod 2) W := by
    have hr : W'.map H.subtype = W := by
      rw [Submodule.map_comap_eq,Submodule.range_subtype,inf_eq_right.mpr hWH]
    rw [←hr,Submodule.finrank_map_subtype_eq]
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W'
  have hdimD : finrank (ZMod 2) D = finrank (ZMod 2) H - finrank (ZMod 2) W := by
    change finrank (ZMod 2) W' + finrank (ZMod 2) D = finrank (ZMod 2) H at hd
    omega
  let : Finite D := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective enc hinj
  rwa [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D),Nat.card_zmod,hdimD] at hc
end Representation.BinaryHyperplaneDisplacement

