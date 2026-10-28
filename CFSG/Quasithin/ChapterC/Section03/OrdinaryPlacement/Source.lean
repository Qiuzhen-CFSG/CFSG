module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.Preparation
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# C.3.2–3 for the original normalized A₅ block

Saturation at the actual radical controls the projection of the original
module into an ordinary component. Irreducibility places that module in the
component. Perfect projection and C-component minimality then place L itself
there. Distinct ordinary components commute, so the normalizer of this
nonabelian L preserves the same component. All ambient subgroup maps remain
literal; no abstract replacement of L, V or the component is made.
Source: Aschbacher–Smith C.3.2–3, printed p.149, applied in 4.3.2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- C.3.2 in the original normalized A₅-block setting: the unchanged actor
is contained in every original ordinary component. -/
theorem alternatingFive_le_ordinary_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : M ≤ normalizer (L : Set G)) (hb : IsAlternatingBlock L 5)
    (hu : (blockU L).map L.subtype = V)
    (K : Subgroup H) (hK : IsComponent H K) : L ≤ K.map H.subtype := by
  have he := h.normalized_span_eq hn
  have hLH := h.component_le.trans h.local_le
  have hVL : V ≤ L := he ▸ h.module_le
  have hVH := hVL.trans hLH
  have hRH := h.radical_le.trans h.local_le
  let A := L.subgroupOf H
  let B := M.subgroupOf H
  let Q := R.subgroupOf H
  let U := V.subgroupOf H
  have hAB : A ≤ B := subgroupOf_mono H h.component_le
  have hUA : U ≤ A := subgroupOf_mono H hVL
  have hBA : B ≤ normalizer (A : Set H) := by
    intro b hb a
    exact hn hb (a : G)
  have hBU : B ≤ normalizer (U : Set H) := by
    have hm : M ≤ normalizer (V : Set G) := by
      rw [←hu]
      exact hn.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
    intro b hb u
    exact hm hb (u : G)
  have hAU := hAB.trans hBU
  have hc : (A.subgroupOf B).IsCComponent := by
    let e := subgroupOfEquivOfLe h.local_le
    have hh := h.component.map_equiv e.symm
    have heq : (L.subgroupOf M).map e.symm.toMonoidHom = A.subgroupOf B := by
      ext b
      constructor
      · rintro ⟨l,hl,rfl⟩
        exact hl
      · intro hl
        exact ⟨e b,hl,e.symm_apply_apply b⟩
    exact heq ▸ hh
  let : Group.IsPerfect (A.subgroupOf B) := hc.perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAB).toMonoidHom) (subgroupOfEquivOfLe hAB).surjective
  have hAK : A ≤ normalizer (K : Set H) :=
    hK.perfect_le_normalizer_of_odd_rank_le_two h.sqtk.stronglyQuasithin A
  let := h.component_outer_solvable K hK
  have hinner : A ≤ K ⊔ centralizer (K : Set H) :=
    perfect_le_sup_centralizer_of_solvable_outer K A hAK
  have hNU : normalizer (U : Set H) ≤ B := by
    rw [←subgroupOf_normalizer_eq hVH]
    intro a ha
    exact h.module_normalizer ⟨a.property,ha⟩
  have hNQ : normalizer (Q : Set H) ≤ B := by
    rw [←subgroupOf_normalizer_eq hRH]
    intro a ha
    exact h.normalizer_le ⟨a.property,ha⟩
  have hsat : ∀ P : Subgroup H, IsPGroup 2 P → B ≤ normalizer (P : Set H) → P ≤ Q := by
    intro P hp hBP
    exact le_of_normalizer_le_normalizer_of_pCore_normalizer_le Q P
      h.isRadical.isPGroup hp h.isRadical.2.le (hNQ.trans hBP)
  have hnc : ¬U ≤ centralizer (K : Set H) := by
    intro hh
    exact h.component_not_le K hK
      ((le_centralizer_iff.mp hh).trans ((Subgroup.centralizer_le_normalizer _).trans hNU))
  have hirr : ∀ W : Subgroup H, W ≤ U → A ≤ normalizer (W : Set H) → W ≠ ⊥ → U ≤ W := by
    intro W hWU hAW hne
    have hWV : W.map H.subtype ≤ V := by
      have hh := map_mono (f := H.subtype) hWU
      rwa [map_subgroupOf_eq_of_le hVH] at hh
    have hLW : L ≤ normalizer (W.map H.subtype : Set G) := by
      intro l hl
      exact W.le_normalizer_map H.subtype ⟨⟨l,hLH hl⟩,hAW hl,rfl⟩
    have hbot : W.map H.subtype ≠ ⊥ :=
      fun hh => hne ((W.map_eq_bot_iff_of_injective H.subtype_injective).mp hh)
    have hi := block_module_irreducible_ambient hb hu _ hWV hLW hbot
    intro u hu
    exact (mem_map_iff_mem H.subtype_injective).mp (hi hu)
  have hQA : ⁅Q,A⁆ ≤ U := by
    have hh := h.normalized_radical_commutator_le_module hn hb hu
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hRH,
      map_subgroupOf_eq_of_le hLH,map_subgroupOf_eq_of_le hVH]
    exact hh
  have hmoved : U = ⁅U,A⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hLH,map_subgroupOf_eq_of_le hVH]
    exact he ▸ h.module_commutator
  have hp : IsPGroup 2 U := h.module_elementary.isPGroup.comap_subtype
  have hUK : U ≤ K := hK.module_le_of_stabilizer_saturation hUA hAB hBU hinner
    hp hmoved hQA hsat hirr hnc
  have hLK : A ≤ K := cComponent_le_of_inner_product_module K A B U hAB hc hBA
    hUA hUK hAU hNU hinner hnc
  have hh := map_mono (f := H.subtype) hLK
  rwa [map_subgroupOf_eq_of_le hLH] at hh

/-- C.3.3 in the original normalized A₅-block setting: M preserves the
same actual ordinary component containing L. -/
theorem alternatingFive_normalizes_ordinary_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : M ≤ normalizer (L : Set G)) (hb : IsAlternatingBlock L 5)
    (hu : (blockU L).map L.subtype = V)
    (K : Subgroup H) (hK : IsComponent H K) :
    M ≤ normalizer (K.map H.subtype : Set G) := by
  have hLH := h.component_le.trans h.local_le
  have hLK := h.alternatingFive_le_ordinary_component hn hb hu K hK
  have hlK : L.subgroupOf H ≤ K := by
    intro l hl
    exact (mem_map_iff_mem H.subtype_injective).mp (hLK hl)
  let := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let : Group.IsPerfect (L.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLH).symm.surjective
  have hne : ⁅L.subgroupOf H,L.subgroupOf H⁆ ≠ ⊥ := by
    rw [commutator_eq_self]
    intro hh
    apply h.component.ne_bot
    have hLbot : L = ⊥ := by
      have hh' := congrArg (map H.subtype) hh
      simpa only [map_subgroupOf_eq_of_le hLH,Subgroup.map_bot] using hh'
    rw [hLbot,bot_subgroupOf]
  have hnorm := hK.normalizer_le_of_nonabelian_subgroup hlK hne
  intro m hm
  have hml : (⟨m,h.local_le hm⟩ : H) ∈ normalizer (L.subgroupOf H : Set H) := by
    intro l
    exact hn hm (l : G)
  exact K.le_normalizer_map H.subtype ⟨⟨m,h.local_le hm⟩,hnorm hml,rfl⟩

end CFSG.Quasithin.ChapterC.HypothesisC28
