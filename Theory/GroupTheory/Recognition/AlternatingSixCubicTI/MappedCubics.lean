module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.NativeCubics
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.SymmetricCore

/-!
# Cubic geometry through the original symmetric embedding

The native cubic-normalizer and two-cubic generation statements are transported through an injective copy of the four-letter symmetric group.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G:Type*} [Group G]

theorem mapped_cubic_normalizer_card (f:Four→*G) (hf:Function.Injective f):
    Nat.card (f.range⊓normalizer (NativeFour.cubic.map f:Set G):Subgroup G)=6 := by
  have he:(normalizer (NativeFour.cubic:Set Four)).map f=
      f.range⊓normalizer (NativeFour.cubic.map f:Set G) := by
    have hc:=comap_normalizer_eq_of_le_range (map_le_range f NativeFour.cubic)
    rw [comap_map_eq_self (show f.ker≤NativeFour.cubic by rw [f.ker_eq_bot_iff.mpr hf]; exact bot_le)] at hc
    rw [←hc,map_comap_eq,inf_comm]
  rw [←he,card_map_of_injective hf,NativeFour.cubic_normalizer_card]

theorem mapped_core_le_sup_cubics (f:Four→*G) (hf:Function.Injective f)
    (U V:Subgroup G) (hU:Nat.card U=3) (hV:Nat.card V=3)
    (hUH:U≤f.range) (hVH:V≤f.range) (hne:U≠V):core.map f≤U⊔V := by
  have hcU:Nat.card (U.comap f)=3 := by
    rw [Nat.card_congr ((U.comap f).equivMapOfInjective f hf).toEquiv,map_comap_eq_self hUH,hU]
  have hcV:Nat.card (V.comap f)=3 := by
    rw [Nat.card_congr ((V.comap f).equivMapOfInjective f hf).toEquiv,map_comap_eq_self hVH,hV]
  have hne':U.comap f≠V.comap f := by
    intro hh
    apply hne
    have hm:=congrArg (fun J:Subgroup Four=>J.map f) hh
    rwa [map_comap_eq_self hUH,map_comap_eq_self hVH] at hm
  have hh:=map_mono (f:=f) (NativeFour.core_le_sup_cubics _ _ hcU hcV hne')
  rwa [Subgroup.map_sup,map_comap_eq_self hUH,map_comap_eq_self hVH] at hh
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
