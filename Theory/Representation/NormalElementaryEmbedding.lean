module
public import Theory.Representation.NormalElementaryQuotient

/-!
# Inclusions of normal elementary quotient modules

Two normal elementary subgroups with the same centralizer carry compatible
faithful actions of the literal common quotient. Their original subgroup
inclusion is an injective binary linear intertwiner. This retains the
canonical quotient map while comparing their moved sections.
Source application: Aschbacher–Smith C.2.7(3)(a), pp.146–147.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
  (U V : Subgroup G) [U.Normal] [V.Normal]
  [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
  (hUV : U ≤ V) (q : G →* H) (hq : Function.Surjective q)
  (hU : q.ker = centralizer (U : Set G))
  (hV : q.ker = centralizer (V : Set G))

noncomputable abbrev inclusionLinear : Additive U →ₗ[ZMod 2] Additive V :=
  (Subgroup.inclusion hUV).toAdditive.toZModLinearMap 2

omit [U.Normal] [V.Normal] in
theorem inclusionLinear_injective : Function.Injective (inclusionLinear U V hUV) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z : Additive V => (z.toMul : G)) hxy

theorem inclusionLinear_intertwines (g : H) (v : Additive U) :
    inclusionLinear U V hUV (representation U q hq hU g v) =
      representation V q hq hV g (inclusionLinear U V hUV v) := by
  obtain ⟨a,rfl⟩ := hq g
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((representation U q hq hU (q a) v).toMul : G) =
    ((representation V q hq hV (q a) (inclusionLinear U V hUV v)).toMul : G)
  rw [representation_apply,representation_apply]
  rfl

end Representation.NormalElementaryQuotient
