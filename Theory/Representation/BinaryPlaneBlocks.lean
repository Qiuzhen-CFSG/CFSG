module
public import Theory.Representation.BinaryPlaneSolvable

/-!
# Faithful actions on two binary plane blocks

For a faithful binary representation with an invariant plane and a plane
quotient, the kernel of the joint block action is an elementary two-group.
A trivial two-core therefore makes the block action faithful. Marking both
binary plane linear groups gives a faithful action in `S₃ × S₃`.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
namespace Representation
open BinaryLinear.SmallParabolicLevi
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
/-- With trivial two-core, the two diagonal plane actions jointly are faithful. -/
theorem exists_faithful_symmetricThree_pair_of_plane
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (U : Subrepresentation ρ) (hU : finrank (ZMod 2) U.toSubmodule = 2)
    (hq : finrank (ZMod 2) (V ⧸ U.toSubmodule) = 2) (hc : pCore 2 G = ⊥) :
    ∃ f : G →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)), Function.Injective f := by
  let a : G →* BinaryLinear.GL V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have ha (g : G) : a g ∈ BinaryLinear.parabolic U.toSubmodule := by
    intro w
    change ρ g w ∈ U.toSubmodule ↔ w ∈ U.toSubmodule
    constructor
    · intro hw
      have he := U.apply_mem_toSubmodule g⁻¹ hw
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using he
    · exact fun hw => U.apply_mem_toSubmodule g hw
  let f := a.codRestrict (BinaryLinear.parabolic U.toSubmodule) ha
  have hfi : Function.Injective f := by
    intro g k h
    apply hf
    apply LinearMap.ext
    intro w
    exact congrArg (fun e : BinaryLinear.parabolic U.toSubmodule => e.val w) h
  let b := blockAction U.toSubmodule
  have hb : IsElementaryAbelian 2 b.ker := by
    apply BinaryTransvectionGroups.elementaryAbelian_of_le_radical
      ((BinaryLinear.parabolic U.toSubmodule).subtype.comp b.ker.subtype)
      (Subtype.val_injective.comp Subtype.val_injective) U.toSubmodule
    intro k
    exact (ker_blockAction U.toSubmodule).le k.property
  let k := b.comp f
  have hk : IsPGroup 2 k.ker := (hb.isPGroup 2 b.ker).comap_of_injective f hfi
  have hkle : k.ker ≤ pCore 2 G := le_sSup ⟨inferInstance,hk⟩
  have hki : Function.Injective k := (MonoidHom.ker_eq_bot_iff k).mp
    (bot_unique (hkle.trans_eq hc))
  let eU : U.toSubmodule ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hU)
  let eQ : (V ⧸ U.toSubmodule) ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hq)
  let e := ((linearGroupCongr eU).trans linearTwoEquivSymmetricThree).prodCongr
    ((linearGroupCongr eQ).trans linearTwoEquivSymmetricThree)
  exact ⟨e.toMonoidHom.comp k,e.injective.comp hki⟩
end Representation
