module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneSource
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.PlaneCentralizers

/-!
# The source plane and its elementary eight have the same centralizer

The root four lies in both subgroups, so any centralizer lies in R=C_G(E).
The literal UT3(F4) root calculation then identifies that centralizer with
the original plane. This proves the faithful normalizer-action kernel and
makes every normalizer of its core eight normalize the plane itself.
Source: Aschbacher, Sporadic Groups (1994),45.6, printed p.244.
-/

@[expose] public section
open Subgroup
open Theory.GroupTheory.HyperbolicRecognition
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

theorem plane_subgroup_centralizer (h:IsType z) (V U:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    (hEU:P.E≤U) (hUV:U≤V) (hU:4<Nat.card U) : Subgroup.centralizer (U:Set G)=V := by
  let := hV.2.1
  have hVR := P.large_elementary_le_R h V hV.1 hV.2.2.ge
  have hUR := hUV.trans hVR
  obtain ⟨e⟩:=P.nonempty_rootEquiv h
  let V':=V.subgroupOf P.R
  let U':=U.subgroupOf P.R
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.subgroupOf hVR
  have hVc : Nat.card V'=16 := (Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv).trans hV.2.2
  have hUc : 4<Nat.card U' := by rwa [Nat.card_congr (subgroupOfEquivOfLe hUR).toEquiv]
  have he := transported_big_plane_centralizer e V' U' hVc (subgroupOf_mono P.R hUV) hUc
  apply le_antisymm
  · intro x hx
    have hxR : x∈P.R := (P.R_eq_centralizer_E h).ge (fun y hy=>hx y (hEU hy))
    have hh : (⟨x,hxR⟩:P.R)∈Subgroup.centralizer (U':Set P.R) :=
      fun y hy=>Subtype.ext (hx y hy)
    change (⟨x,hxR⟩:P.R)∈V'
    exact he ▸ hh
  · intro x hx u hu
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=V)).comm ⟨u,hUV hu⟩ ⟨x,hx⟩)

theorem plane_centralizer (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) : Subgroup.centralizer (V:Set G)=V :=
  P.plane_subgroup_centralizer h V V hV (P.E_le_plane h V hV) le_rfl (by rw [hV.2.2]; decide)

theorem plane_core_eight_centralizer (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    Subgroup.centralizer (V⊓core z:Set G)=V :=
  P.plane_subgroup_centralizer h V (V⊓core z) hV
    (le_inf (P.E_le_plane h V hV) (P.E_le_core h)) inf_le_left
    (by rw [P.plane_inf_core_card h V hV]; decide)
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
