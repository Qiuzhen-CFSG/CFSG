module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.MaximumPlanes
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# The exact elementary-sixteen family of the original Sylow

The native UT₃(F₄) planes and the source large-elementary bound identify
all elementary subgroups of maximum order in T. Their ambient images
have intersection E and join R, and both are normalized by N_G(E).
The record retains literal subgroups for weak closure and normalizer action.

Source: Aschbacher, *Sporadic Groups* (1994),45.5(3), printed p.244.
-/

@[expose] public section
open Subgroup
open Theory.GroupTheory.HyperbolicRecognition
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

theorem elementary_card_le_sixteen (h : IsType z) (V : Subgroup G)
    (hVT : V≤P.T) [IsElementaryAbelian 2 V] : Nat.card V≤16 := by
  by_cases hv : Nat.card V<16
  · exact hv.le
  have hVR := P.large_elementary_le_R h V hVT (by omega)
  obtain ⟨e⟩ := P.nonempty_rootEquiv h
  let V' := V.subgroupOf P.R
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.subgroupOf hVR
  let W := V'.map e.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hw : Nat.card W=Nat.card V := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv]
  rcases elementary_le_rootPlane W with hW | hW
  · have hh := Nat.card_le_card_of_injective (inclusion hW) (inclusion_injective hW)
    rwa [hw,card_rootPlane₁] at hh
  · have hh := Nat.card_le_card_of_injective (inclusion hW) (inclusion_injective hW)
    rwa [hw,card_rootPlane₂] at hh

/-- The source pair consists of precisely the elementary sixteen-groups of T. -/
structure PlanePair where
  first : Subgroup G
  second : Subgroup G
  first_le : first≤P.R
  second_le : second≤P.R
  first_elementary : IsElementaryAbelian 2 first
  second_elementary : IsElementaryAbelian 2 second
  first_card : Nat.card first=16
  second_card : Nat.card second=16
  distinct : first≠second
  inf_eq : first⊓second=P.E
  sup_eq : first⊔second=P.R
  first_normalized : P.N≤normalizer (first:Set G)
  second_normalized : P.N≤normalizer (second:Set G)
  exhaustive : ∀V:Subgroup G,
    (V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) ↔ V=first ∨ V=second

theorem exists_planePair (h : IsType z) : Nonempty P.PlanePair := by
  obtain ⟨E₁,E₂,h₁,h₂,hc₁,hc₂,hne,hi,hn₁,hn₂,hall⟩ := P.exists_two_N_normal_root_planes h
  let V₁:=E₁.map P.R.subtype
  let V₂:=E₂.map P.R.subtype
  have h₁' : IsElementaryAbelian 2 V₁ := by let := h₁; exact IsElementaryAbelian.map P.R.subtype
  have h₂' : IsElementaryAbelian 2 V₂ := by let := h₂; exact IsElementaryAbelian.map P.R.subtype
  have hc₁' : Nat.card V₁=16 := (card_map_of_injective P.R.subtype_injective).trans hc₁
  have hc₂' : Nat.card V₂=16 := (card_map_of_injective P.R.subtype_injective).trans hc₂
  have hne' : V₁≠V₂ := fun he=>hne (map_injective P.R.subtype_injective he)
  have hi' : V₁⊓V₂=P.E := by rw [←map_inf _ _ _ P.R.subtype_injective]; exact hi
  have hRN : P.R≤P.N := (show P.R≤P.T from le_sup_left).trans (P.T_le_N h)
  have hs : V₁⊔V₂=P.R := by
    have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes V₁ V₂
      ((map_subtype_le E₂).trans (hRN.trans hn₁))
    rw [hc₁',hc₂',hi',P.E_card h] at he
    apply eq_of_le_of_card_ge (sup_le (map_subtype_le _) (map_subtype_le _))
    rw [P.R_card h]
    change 64≤Nat.card (V₁⊔V₂:Subgroup G)
    omega
  refine ⟨⟨V₁,V₂,map_subtype_le _,map_subtype_le _,h₁',h₂',hc₁',hc₂',hne',hi',hs,hn₁,hn₂,?_⟩⟩
  intro V
  constructor
  · rintro ⟨hVT,hV,hVc⟩
    let := hV
    have hVR := P.large_elementary_le_R h V hVT hVc.ge
    let V' := V.subgroupOf P.R
    have hV' : IsElementaryAbelian 2 V' := IsElementaryAbelian.subgroupOf hVR
    have hc' : Nat.card V'=16 := (Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv).trans hVc
    rcases (hall V').mp ⟨hV',hc'⟩ with he | he
    · left
      have hm := congrArg (map P.R.subtype) he
      rwa [map_subgroupOf_eq_of_le hVR] at hm
    · right
      have hm := congrArg (map P.R.subtype) he
      rwa [map_subgroupOf_eq_of_le hVR] at hm
  · rintro (rfl | rfl)
    · exact ⟨(map_subtype_le E₁).trans le_sup_left,h₁',hc₁'⟩
    · exact ⟨(map_subtype_le E₂).trans le_sup_left,h₂',hc₂'⟩

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
