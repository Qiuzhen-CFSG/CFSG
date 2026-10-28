module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CenterActionSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CentralProjectionSource
public import Theory.GroupTheory.CenterPairMarks
/-! # The original source center split for a normal component
Each central Sylow element acts on the component by its own Sylow center.
Centerlessness makes the implementer central in the full original Sylow.
The two factors therefore split its center; the component factor is the
order-two center of the actual component Sylow. The other factor is the
intersection with the original two-core, not an abstract kernel substitute.
Source: Aschbacher--Smith 2.5.8(4), printed p.557.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.normal_component_center_split
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel L) :
    let Y:=(S:Subgroup H).map H.subtype
    centerIn Y=(centerIn Y⊓L)⊔(centerIn Y⊓twoCore H) ∧
      Disjoint (centerIn Y⊓L) (centerIn Y⊓twoCore H) ∧
      Nat.card (centerIn Y⊓L:Subgroup G)=2 ∧
      centerIn Y⊓L=centerIn (Y⊓L) := by
  let Y:=(S:Subgroup H).map H.subtype
  have hc:=MathieuSourceSetup.component_center_eq_bot c hG hempty hgen
  have hYL:Y≤normalizer (L:Set G):=(map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have hsplit:=center_split_of_inner_pointwise_actions Y L hYL hc (by
    intro y hy
    obtain ⟨u,hu,_,ha⟩:=MathieuSourceSetup.center_action_inner c hG hempty hgen hb y hy
    exact ⟨u,hu,ha⟩)
  have hCZ:centerIn Y⊓twoCore H=centerIn Y⊓centralizer (L:Set G):=by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    ext a
    exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,h.1.1,h.2⟩⟩
  have hdis:Disjoint (centerIn Y⊓L) (centerIn Y⊓centralizer (L:Set G)):=by
    apply disjoint_iff.mpr
    apply bot_unique
    intro a ha
    have hh:(⟨a,ha.1.2⟩:L)∈center L:=mem_center_iff.mpr (fun l=>Subtype.ext (ha.2.2 l l.property))
    have he:=mem_bot.mp (hc ▸ hh)
    exact congrArg Subtype.val he
  have hPc:Nat.card (centerIn (Y⊓L))=2:=by
    have hp:SourceSylowTwoShape (Y.subgroupOf L):=
      (MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.2.2
    let e:(Y.subgroupOf L)≃*(Y⊓L:Subgroup G):={
      toFun u:=⟨u.val.val,u.property,u.val.property⟩
      invFun u:=⟨⟨u,u.property.2⟩,u.property.1⟩
      left_inv _:=rfl
      right_inv _:=rfl
      map_mul' _ _:=rfl }
    rw [centerIn_eq_map_center,card_map_of_injective (Y⊓L:Subgroup G).subtype_injective]
    exact (Nat.card_congr (centerCongr e).toEquiv).symm.trans hp.center_card
  obtain ⟨hcard,he⟩:=center_factor_card_two_of_sylow_center Y L hYL hPc
  change centerIn Y=(centerIn Y⊓L)⊔(centerIn Y⊓twoCore H) ∧
    Disjoint (centerIn Y⊓L) (centerIn Y⊓twoCore H) ∧
    Nat.card (centerIn Y⊓L:Subgroup G)=2 ∧ centerIn Y⊓L=centerIn (Y⊓L)
  rw [hCZ]
  exact ⟨hsplit,hdis,hcard,he⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
