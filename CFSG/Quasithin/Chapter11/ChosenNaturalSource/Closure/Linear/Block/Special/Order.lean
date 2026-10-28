module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Sections
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The order of the original special factor

The starred closure has order q², and its kernel is S. The central
splitting S=V C_U(L) is direct on V, giving |U|=q⁵ |C_U(L)|.
The second product formula U=(U∩L)C_U(L) then counts the literal
quotient (U∩L)/C_{U∩L}(L), without assuming that U lies in L.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

theorem closureStarProjection_kernel
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    (Hypothesis.UStarProjection (setup E) hUT).ker = (threeCore E x y).subgroupOf E.W := by
  have hUI : E.W ≤ threeGroup E x y := by
    rw [threeGroup_eq_join d hUT hf]
    exact le_sup_right
  have hs := d.S_eq_star_kernel hUT hf
  ext u
  change Hypothesis.UStarProjection (setup E) hUT u = 1 ↔ (u : G) ∈ threeCore E x y
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 ↥(L ⊔ (T : Subgroup G)))
    (inclusion (hUT.trans le_sup_right) u) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hu
    exact hs.ge ⟨hUI u.property, mem_map_of_mem _ hu⟩
  · intro hu
    obtain ⟨v, hv, he⟩ := (hs.le hu).2
    exact (Subtype.ext he : v = inclusion (hUT.trans le_sup_right) u) ▸ hv

theorem chosen_card : Nat.card V = (2 ^ E.input.field.degree) ^ 3 := by
  change Nat.card (setup E).V = _
  rw [Nat.card_congr d.coordinates.toEquiv]
  change Nat.card (Fin 3 → E.input.field.Carrier) = _
  rw [Nat.card_fun, Nat.card_fin, d.field_card]

theorem point_card : Nat.card E.V₁ = 2 ^ E.input.field.degree := by
  let f : E.V₁ → d.point := fun v =>
    ⟨(d.coordinates ⟨v,E.V₁_le v.property⟩).toAdd, (d.point_mem _).mp v.property⟩
  have hi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    exact congrArg (fun z : (setup E).V => (z : G)) (d.coordinates.injective
      (congrArg (fun z : d.point => Multiplicative.ofAdd z.val) he))
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨v,hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd w.val)
    have hp : (v : G) ∈ E.V₁ := (d.point_mem v).mpr (by rw [hv]; exact w.property)
    exact ⟨⟨v,hp⟩, Subtype.ext (congrArg Multiplicative.toAdd hv)⟩
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),
    Module.natCard_eq_pow_finrank (K := E.input.field.Carrier), d.point_dimension,
    pow_one, d.field_card]

theorem threeCore_card
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    Nat.card (threeCore E x y) = (2 ^ E.input.field.degree) ^ 3 *
      Nat.card (E.W ⊓ centralizer (L : Set G) : Subgroup G) := by
  rw [threeCore_split E d hUT hf hc, threeCore_centralizer E d hUT hf hc]
  rw [card_sup_eq_mul_of_normalizes_of_disjoint, chosen_card E d]
  · exact (inf_le_right.trans (centralizer_le D.le_component)).trans
      (centralizer_le_normalizer _)
  · apply disjoint_iff.mpr
    exact bot_unique ((inf_le_inf_left V inf_le_right).trans (chosen_fixed_eq_bot E d).le)

set_option backward.isDefEq.respectTransparency false in
theorem closure_card_mul_centralizer
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    Nat.card E.W = (2 ^ E.input.field.degree) ^ 5 *
      Nat.card (E.W ⊓ centralizer (L : Set G) : Subgroup G) := by
  let π := Hypothesis.UStarProjection (setup E) hUT
  have hker : Nat.card π.ker = Nat.card (threeCore E x y) := by
    rw [closureStarProjection_kernel E d hUT hf]
    exact Nat.card_congr (subgroupOfEquivOfLe
      (hc.le.trans (triple_le_closure E x y))).toEquiv
  have hi : π.ker.index = 2 ^ (2 * E.input.field.degree) := by
    rw [index_ker, MonoidHom.range_eq_top_of_surjective π
      (Hypothesis.UStarProjection_surjective (D := setup E) hUT), Nat.card_congr (topEquiv : (⊤ : Subgroup ((setup E).star (setup E).U)) ≃* (setup E).star (setup E).U).toEquiv]
    exact d.card_star_U hUT hf
  have hh := π.ker.card_mul_index
  rw [hker, hi, threeCore_card E d hUT hf hc] at hh
  change _ = Nat.card E.W at hh
  rw [← hh, Nat.mul_comm 2 E.input.field.degree, pow_mul]
  ring

theorem specialFactor_card
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    Nat.card (SpecialFactor E) = (2 ^ E.input.field.degree) ^ 5 := by
  let A := componentPart E
  let C := E.W ⊓ centralizer (L : Set G)
  have hn : C ≤ normalizer (A : Set G) := by
    apply (inf_le_right.trans (centralizer_le inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A C hn
  have hjoin : A ⊔ C = E.W := (closure_split E d hUT hf hc).symm
  have hden : Nat.card (centralPart E) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [Nat.card_congr ((centralPart E).equivMapOfInjective A.subtype A.subtype_injective).toEquiv]
    have he : (centralPart E).map A.subtype = A ⊓ C := by
      rw [centralPart_map]
      change E.W ⊓ L ⊓ centralizer (L : Set G) = (E.W ⊓ L) ⊓ (E.W ⊓ centralizer (L : Set G))
      ext z
      simp only [mem_inf]
      tauto
    rw [he]
  have hq := (centralPart E).card_mul_index
  rw [index_eq_card, hden] at hq
  rw [hjoin, closure_card_mul_centralizer E d hUT hf hc, ← hq] at hprod
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card (A ⊓ C : Subgroup G) from Nat.card_pos)
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card C from Nat.card_pos)
  simpa only [Nat.mul_assoc] using hprod

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
