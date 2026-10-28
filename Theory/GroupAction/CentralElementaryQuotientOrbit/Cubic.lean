module

public import Theory.GroupAction.CentralElementaryQuotientOrbit
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.CubicAction

/-!
# Cubics fix no nonidentity element of the symmetric-four core

The cyclic subgroup of a fixed core element is invariant. Cubic
irreducibility and the core order four exclude a nontrivial cyclic
subgroup, since every core element has square one.

Source: Aschbacher–Smith, J.4.4(2), printed p.441.
-/

public section
open Subgroup
namespace Matrix.PSL3Two.ParabolicCoreModel
variable {G:Type*} [Group G] [Finite G]

theorem core_cubic_fixed (e:G≃*Equiv.Perm (Fin 4)) (c:G) (hc:orderOf c=3)
    (x:G) (hx:x∈pCore 2 G) (hf:c*x*c⁻¹=x) : x=1 := by
  let := (core_data e).1
  have hn : c∈normalizer (zpowers x : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (c*x*c⁻¹)=zpowers x
    rw [hf]
  rcases cubic_invariant_core e c hc (zpowers x) (zpowers_le.mpr hx) hn with h | h
  · exact (zpowers_eq_bot.mp h)
  · have hcard := congrArg (fun K:Subgroup G => Nat.card K) h
    rw [Nat.card_zpowers,(core_data e).2] at hcard
    have hb := orderOf_le_of_pow_eq_one (by decide : 0<2)
      (elemPow_eq_one_of_isElementaryAbelian x hx)
    omega

end Matrix.PSL3Two.ParabolicCoreModel
