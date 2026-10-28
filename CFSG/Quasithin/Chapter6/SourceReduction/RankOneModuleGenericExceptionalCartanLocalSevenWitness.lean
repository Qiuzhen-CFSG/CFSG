module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenAction
public import Theory.SpecificGroups.Alternating.SevenCubicInversion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition

/-!
# The complete local Cartan witness in the selected A7 row

The literal action on C/O2(C) is cubic. Its restriction to A intersect C
is injective because this intersection is odd and the quotient is centerless.
The already constructed escaping cubic therefore equals that intersection.
Intersecting the original permuting Cartan--Sylow product with the same
normal C gives a subgroup in which T intersect C has index three.
The seven-point inversion theorem lifts an inverter of the specified cubic
from that original Sylow, with no splitting assumption on the two-core.

This completes every field of LocalCartanWitness for the selected A7
component. The existing recognition theorem then gives degree two and the
full CartanExceptionalConclusion for the unchanged W, including relative
relocation to the whole omega centralizer. Both original Hall conditions,
quotient maps and arbitrary Sylow/module choices are retained.

Exhaustive component selection, the triple-cover exclusion and the surviving
binary-triality branch remain obligations of the full local source theorem.
Source: Aschbacher--Smith 5.1.13, printed pp.637--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Every cubic of the original Cartan in the selected A7 component is
inverted by an element of the original Sylow intersection. -/
theorem alternating_seven_cubic_inverted
    {T : Sylow 2 G} {L W H A B K Y D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7)
    (hDA : D ≤ A) (hDC : D ≤ C.map Y.subtype) (hD : Nat.card D = 3) :
    ∃ t ∈ (T : Subgroup G) ⊓ C.map Y.subtype,
      ∀ d ∈ D, t*d*t⁻¹=d⁻¹ := by
  let f := normalQuotientAction C (pCore 2 C)
  let AY := A.subgroupOf Y
  let TY := (T : Subgroup G).subgroupOf Y
  let E := AY.subgroupOf C
  let J := (AY ⊔ TY).subgroupOf C
  let e := hm.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (alternatingGroup (Fin 7)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  let j : E →* A :=
    { toFun x := ⟨x.val.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) he)))
  have hoE : Odd (Nat.card E) := hoA.of_dvd_nat (card_dvd_of_injective j hj)
  have hiE : Function.Injective ((f.comp C.subtype).comp E.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hqx : QuotientGroup.mk' (pCore 2 C) x.val = 1 := by
      apply conj_injective_of_center_eq_bot hz
      rw [←normalQuotientAction_inner,map_one]
      exact hx
    have hd : Disjoint E (pCore 2 C) := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
      rw [hk]
      exact hoE.coprime_two_right.pow_right k
    exact Subtype.ext (disjoint_def.mp hd x.property ((QuotientGroup.eq_one_iff _).mp hqx))
  have hDc := alternating_seven_action_card_three h hH hgen c hK hKT horbit
    hY hescape C hC hKC (.inl hm)
  have hEupper : Nat.card E ≤ 3 := by
    let g : E →* AY.map f :=
      { toFun x := ⟨f x.val.val,mem_map_of_mem f x.property⟩
        map_one' := Subtype.ext (map_one f)
        map_mul' _ _ := Subtype.ext (map_mul f _ _) }
    have hi : Function.Injective g := fun x y he => hiE (congrArg Subtype.val he)
    exact (Nat.card_le_card_of_injective g hi).trans_eq hDc
  have hDY : D ≤ Y := hDC.trans (map_subtype_le C)
  have hDYC : D.subgroupOf Y ≤ C := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hDC hx
    exact (show y=x from Subtype.ext he) ▸ hy
  let DC := (D.subgroupOf Y).subgroupOf C
  have hDCc : Nat.card DC = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDYC).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv,hD]
  have hDE : DC ≤ E := fun _ hx => hDA hx
  have hEc : Nat.card E = 3 := le_antisymm hEupper
    (hDCc ▸ Nat.card_le_card_of_injective (inclusion hDE) (inclusion_injective hDE))
  have hTY := hH.1.1.2.trans hY.2
  let S0 := T.subtype hTY
  obtain ⟨S,hS⟩ := S0.exists_subgroupOf_eq_of_normal C
  have hSJ : (S : Subgroup C) ≤ J := by
    rw [hS]
    exact comap_mono le_sup_right
  have hEc' : Nat.card (AY ⊓ C : Subgroup Y) = 3 := by
    rw [←hEc]
    change Nat.card (AY ⊓ C : Subgroup Y) = Nat.card (AY.subgroupOf C)
    rw [←inf_subgroupOf_right AY C]
    exact (Nat.card_congr (subgroupOfEquivOfLe (show AY ⊓ C ≤ C from inf_le_right)).toEquiv).symm
  have hSc : Nat.card S = Nat.card (TY ⊓ C : Subgroup Y) := by
    rw [hS]
    change Nat.card (TY.subgroupOf C) = _
    rw [←inf_subgroupOf_right TY C]
    exact Nat.card_congr (subgroupOfEquivOfLe (show TY ⊓ C ≤ C from inf_le_right)).toEquiv
  have hoAY : Odd (Nat.card AY) := by
    change Odd (Nat.card (A.subgroupOf Y))
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
    exact hoA.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hcop : Nat.Coprime (Nat.card AY) (Nat.card TY) := by
    obtain ⟨k,hk⟩ := S0.isPGroup'.exists_card_eq
    change Nat.card TY = 2 ^ k at hk
    rw [hk]
    exact hoAY.coprime_two_right.pow_right k
  have hperm : (AY : Set Y) * (TY : Set Y) = (TY : Set Y) * (AY : Set Y) := by
    simpa using c.image_intersection_permutes_sylow h.sylow_normalizes hTY (MonoidHom.id Y)
  have hJc : Nat.card J = 3 * Nat.card S := by
    rw [card_subgroupOf_sup_of_coprime_permutable AY TY C hcop hperm,hEc',←hSc]
  obtain ⟨t,ht,hinv⟩ := AlternatingSeven.cubic_inverted_of_two_kernel q hq hqk S J DC
    hSJ (hDE.trans (comap_mono le_sup_left)) hJc hDCc
  have htT : (t.val : G) ∈ (T : Subgroup G) := by rw [hS] at ht; exact ht
  refine ⟨t.val,⟨htT,mem_map_of_mem Y.subtype t.property⟩,?_⟩
  intro d hd
  let y : Y := ⟨d,hDY hd⟩
  let x : C := ⟨y,hDYC hd⟩
  exact congrArg (fun z : C => (z.val:G)) (hinv x hd)

/-- The selected A7 row supplies the entire local witness on that same
container, including the actual escaping cubic and its original-Sylow inverter. -/
theorem alternating_seven_local_witness
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7) :
    ∃ D : Subgroup G, LocalCartanWitness T H A Y (C.map Y.subtype) D := by
  obtain ⟨hKR,hR,_⟩ := normal_alternating_seven_residual_and_hall
    h hH hgen c hK hKT horbit hY hescape C hC hKC (.inl hm)
  obtain ⟨D,hDC,hD,hes⟩ := alternating_seven_escaping_cubic
    h hH hgen c hK hKT horbit hY hescape C hC hKC hm
  have hc : (C.map Y.subtype).subgroupOf Y = C :=
    comap_map_eq_self_of_injective Y.subtype_injective C
  let e := C.equivMapOfInjective Y.subtype Y.subtype_injective
  have he : Nonempty (((C.map Y.subtype) ⧸ pCore 2 (C.map Y.subtype)) ≃*
      alternatingGroup (Fin 7)) :=
    ⟨(QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans hm.some⟩
  refine ⟨D,⟨map_subtype_le C,?_,?_,hKR ▸ hKC,hR,.inl he,hDC,hD,hes,?_⟩⟩
  · rw [hc]; exact hC
  · rw [hc]; infer_instance
  · exact alternating_seven_cubic_inverted h hH hgen c hK hKT horbit
      hY hescape C hC hKC hm (hDC.trans inf_le_left) (hDC.trans inf_le_right) hD

/-- The selected A7 row gives the full source conclusion on the original W.
Neither degree two, module coordinates nor omega-centralization is assumed. -/
theorem alternating_seven_cartan_exceptional
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  obtain ⟨D,d⟩ := alternating_seven_local_witness
    h hH hgen c hK hKT horbit hY hescape C hC hKC hm
  exact localCartan_escape_of_witness h hH hgen c hY d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
