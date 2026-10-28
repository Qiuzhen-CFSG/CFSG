module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.SourceChief
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.Mathieu
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.SevenPrimes
public import Theory.SpecificGroups.Rudvalis.Multiplier.Universe

/-!
# Selecting the actual Rudvalis covering

The original source action excludes each of the ten other sporadic rows.
The Rudvalis multiplier bound makes the actual covering kernel at most two;
the original central involution belongs to it and has order two. Thus the
projection on the unchanged component has kernel exactly its cyclic subgroup,
not an unmarked isomorphic central subgroup.

Source: Aschbacher–Smith14.7.68(2), printed p.1071, and I.1.3.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedSporadic_eq_ru_of_point_commutator
    (u : F.U) {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
    (h : SporadicSieve.Case d u Lu α name)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : name = .ru := by
  have hm11 := d.fixedSporadic_ne_m11 u h e
  have hm12 := d.fixedSporadic_ne_m12 u h e
  have hm22 := d.fixedSporadic_ne_m22 u h e
  have hm23 := d.fixedSporadic_ne_m23 u h e
  have hm24 := d.fixedSporadic_ne_m24 u h e
  have hsmall := d.fixedSporadic_not_j2_hs_of_point_commutator u α e h hcomm
  have hj4 := h.not_j4 e
  have hhe := h.not_he e
  have hj3 := h.not_j3
  cases name <;> simp_all
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Theory.GroupTheory Chapter12.Section08 ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem exists_fixedRudvalisCover_of_sporadic
    (u : F.U) {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} {name : SporadicName}
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
    (h : SporadicSieve.Case d u Lu α name)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : Nonempty (d.FixedRudvalisCover u Lu) := by
  have hn := d.fixedSporadic_eq_ru_of_point_commutator u e h hcomm
  subst name
  let J := Lu.subgroupOf (d.fixedCentralizer u)
  let c := d.fixedSporadicCover u h.le_centralizer h.quasisimple e
  let a : J ≃* Lu := subgroupOfEquivOfLe h.le_centralizer
  let f : Lu →* Rudvalis.Model := c.toMonoidHom.comp a.symm.toMonoidHom
  have hf : Function.Surjective f := c.surjective.comp a.symm.surjective
  have hk : Nat.card f.ker ≤ 2 := by
    rw [show f.ker = c.toMonoidHom.ker.map a.toMonoidHom from
      MonoidHom.ker_comp_mulEquiv c.toMonoidHom a.symm,card_map_of_injective a.injective]
    exact Rudvalis.Multiplier.cover_kernel_card_le_two_any_universe c
  have huLu : (u : G) ∈ Lu := d.fixed_mem_component_of_commutator h.generation u h.contains.le
  let uL : Lu := ⟨u,huLu⟩
  let uJ : J := a.symm uL
  have huCenter : uJ ∈ center J := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp y.val.property
  have huOrder : orderOf uJ = 2 := by
    change orderOf (a.symm uL) = 2
    rw [a.symm.orderOf_eq,← orderOf_coe uL]
    exact d.fixedElement_order u h.nontrivial
  have huCore : uJ ∈ pCore 2 J := by
    have hp : IsPGroup 2 (zpowers uJ) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,huOrder,pow_one])
    have hn : (zpowers uJ).Normal := by
      constructor
      intro y hy b
      have hc := (zpowers_le.mpr huCenter) hy
      rw [mem_center_iff.mp hc b]
      simpa using hy
    exact (le_sSup ⟨hn,hp⟩ : zpowers uJ ≤ pCore 2 J) (mem_zpowers uJ)
  have huKer : (u : G) ∈ f.ker.map Lu.subtype := by
    apply mem_map.mpr
    refine ⟨uL,?_,rfl⟩
    change uJ ∈ c.toMonoidHom.ker
    rw [fixedSporadicCover_kernel]
    exact huCore
  refine ⟨⟨f,hf,?_⟩⟩
  apply Eq.symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr huKer)
  rw [card_map_of_injective Lu.subtype_injective,Nat.card_zpowers,
    d.fixedElement_order u h.nontrivial]
  exact hk
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
