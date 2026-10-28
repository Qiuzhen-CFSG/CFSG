module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryModels
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryModule
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementaryBound

/-!
# Three remaining ordinary sporadic quotients for the unitary source

The literal module image has at least 64 elements, excluding the actual
Hall–Janko carrier, whose elementary subgroups have at most sixteen.
The native Mathieu normalizer obstruction excludes M₂₄. Combining both
with the full ordinary catalogue leaves actual central quotient markings
by J₄, He or Ru. Their remaining local recognition is not assumed here.

Source: Aschbacher–Smith C.3.1,C.4.8, pp.149–154, and 4.2.12–13, pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

theorem no_unitary_ordinary_jankoTwo
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  obtain ⟨_,he,_,_,hc,_⟩ := h.unitary_ordinary_module_image a K hK
  let E := ((V.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let := he
  let : IsElementaryAbelian 2 (E.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hb := Sporadic.LeechRelated.J2.ElementarySixteenFusion.elementary_card_le_sixteen
    (E.map e.toMonoidHom)
  rw [card_map_of_injective e.injective] at hb
  change 64 ≤ Nat.card E at hc
  omega

/-- The remaining alternatives retain genuine central quotient equivalences. -/
theorem unitary_ordinary_three_sporadic_models
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    ∃ n : SporadicName, (n = .j4 ∨ n = .he ∨ n = .ru) ∧
      Nonempty (K ⧸ center K ≃* n.Carrier) := by
  obtain ⟨n,hn,⟨e⟩⟩ := h.unitary_ordinary_five_sporadic_models a K hK
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact (h.no_unitary_ordinary_mathieu24 a K hK e).elim
  · exact (h.no_unitary_ordinary_jankoTwo a K hK e).elim
  · exact ⟨.j4,by simp,⟨e⟩⟩
  · exact ⟨.he,by simp,⟨e⟩⟩
  · exact ⟨.ru,by simp,⟨e⟩⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
