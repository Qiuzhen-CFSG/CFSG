module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.DerivedCoreMarking
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedShortSupplement
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.IntrinsicDerivedCore
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The marked short-root commutator belongs to the original natural V

The same endpoint equivalence transports the intrinsic derived subgroup of
its two-core. The concrete core has derived order 64 and center order at most
8. The earlier source commutator theorem then identifies the embedded center
with the original V, without an extra coordinate or V-placement assumption.
The marked short-root word is central in that derived group, so it belongs
to V. Together with the source centralizer supplement this supplies the two
local assertions used in J.4.7, printed p.444.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
open Subgroup
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
open IntrinsicDerivedCore

private def innerDerived : Subgroup second := ⁅pCore 2 second,pCore 2 second⁆

private theorem model_derived_map :
    innerDerived.map second.subtype=⁅secondCore,secondCore⁆ := by
  rw [innerDerived,map_commutator]
  rfl

variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)
  (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic)
  (h:Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)))
  (e:second ≃* p.F₂ B5 X)

include h e

private theorem source_derived_map :
    innerDerived.map ((p.F₂ B5 X).subtype.comp e.toMonoidHom)=sourceDerived p B5 := by
  rw [innerDerived,map_commutator]
  have hc:(pCore 2 second).map ((p.F₂ B5 X).subtype.comp e.toMonoidHom)=p.A B5 := by
    rw [← map_map,pCore_map_iso,p.F₂_core B5 X h,
      map_subgroupOf_eq_of_le (p.A_le_F₂ B5 X)]
  rw [hc]
  rfl

/-- Recognition preserves the order of the actual source derived subgroup. -/
theorem source_derived_card : Nat.card (sourceDerived p B5)=64 := by
  have hf:Function.Injective ((p.F₂ B5 X).subtype.comp e.toMonoidHom) :=
    fun _ _ hh=>e.injective (Subtype.ext hh)
  rw [← source_derived_map p B5 X h e,
    card_map_of_injective hf]
  have hc:=derived_card
  rw [← model_derived_map,card_map_of_injective second.subtype_injective] at hc
  exact hc

/-- Its embedded center is exactly the original natural eight-group V. -/
theorem source_derived_center_eq_V :
    (center (sourceDerived p B5)).map (sourceDerived p B5).subtype=d.V := by
  apply center_sourceDerived_eq_V p B5
  · rw [source_derived_card p B5 X h e]
    decide
  · let em:=innerDerived.equivMapOfInjective second.subtype second.subtype_injective
    let es:=innerDerived.equivMapOfInjective
      ((p.F₂ B5 X).subtype.comp e.toMonoidHom)
      ((p.F₂ B5 X).subtype_injective.comp e.injective)
    have hc:=derived_center_card
    rw [← model_derived_map,← Nat.card_congr (centerCongr em).toEquiv] at hc
    rw [← source_derived_map p B5 X h e,← Nat.card_congr (centerCongr es).toEquiv]
    exact hc

/-- The literal marked short-root commutator lies in the original V. -/
theorem source_short_mem_V : (e modelShort:G)∈d.V := by
  have hf:Function.Injective ((p.F₂ B5 X).subtype.comp e.toMonoidHom) :=
    fun _ _ hh=>e.injective (Subtype.ext hh)
  have hm:modelShort∈(center innerDerived).map innerDerived.subtype := by
    apply (mem_map_iff_mem second.subtype_injective).mp
    rw [map_embeddedCenter _ _ second.subtype_injective,model_derived_map]
    exact short_mem_derived_center
  have hs:=mem_map_of_mem ((p.F₂ B5 X).subtype.comp e.toMonoidHom) hm
  rw [map_embeddedCenter _ _ hf,
    source_derived_map p B5 X h e,source_derived_center_eq_V p B5 X h e] at hs
  exact hs

/-- Both local conclusions use the same original endpoint map and core A. -/
theorem source_short_natural_and_supplement :
    (e modelShort:G)∈d.V ∧
    p.A B5 ⊔ (p.F₂ B5 X ⊓ centralizer ({(e modelShort:G)}:Set G))=p.F₂ B5 X :=
  ⟨source_short_mem_V p B5 X h e,source_shortCentralizer_supplement p B5 X h e⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
