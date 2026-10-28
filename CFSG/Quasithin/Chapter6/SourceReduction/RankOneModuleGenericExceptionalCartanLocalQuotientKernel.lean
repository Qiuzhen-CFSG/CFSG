module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryDegree

/-!
# The kernel of the local Cartan omega-span quotient

In the original local source problem, Y contains the full Sylow two-subgroup
and has nontrivial two-core. Condition (E), via 1.1.4(6), makes this core
self-centralizing. Consequently the original Sylow omega-center lies in
O₂(Y). Its nonidentity elements belong to the original L-span, so the
restriction of Y → Y/O₂(Y) to that span is never injective, and its image
has strictly smaller order.

This is an obstruction to transferring the zero-core binary-triality
argument to the local row: the lower bound on the original omega-span
cannot be transported by an injection into the triality quotient. The
zero-core parabolic marking used in 5.2.2 has different hypotheses.
This calculation does not refute the full source theorem or exclude
the remaining degree-two binary-triality row.

Source: Aschbacher--Smith 1.1.4(6), 5.1.13 and 5.2.2,
printed pp.501,635--638,647--648, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow omega-center is killed by the literal local quotient. -/
theorem Input.local_omega_le_twoCore
    {T : Sylow 2 G} {L W H Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ Y.pCoreIn 2 := by
  have hTY := hH.1.1.2.trans hY.2
  have hQ : Y.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow Y (T.subtype hTY)
    change Y.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf Y).map Y.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTY] at hh
  have hc := Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) ⟨hY.1,hTY⟩
  intro z hz
  have ht := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  exact hc ⟨hTY ht.1, fun q hq => ht.2.2 q (hQ hq)⟩

/-- The original omega-span cannot be injected into Y/O₂(Y) by the quotient map. -/
theorem Input.local_omega_span_quotient_not_injective
    {T : Sylow 2 G} {L W H Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    ¬ Function.Injective ((QuotientGroup.mk' (pCore 2 Y)).comp
      (V.subgroupOf Y).subtype) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let V := conjugateSpanBy Z L
  have hW : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hW h.reduced_le_sylow
      (le_sup_right.trans (reduced_normalizes h.reduced)))
  let := h.reduced.2.1
  have hzZ : (z : G) ∈ Z := (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨h.reduced_le_sylow z.property.1,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property.1,z.property.2.2⟩
  have hzV : (z : G) ∈ V := le_conjugateSpanBy Z L hzZ
  have hzcore : (z : G) ∈ Y.pCoreIn 2 := Input.local_omega_le_twoCore h hH hY hzZ
  obtain ⟨y,hy,he⟩ := hzcore
  change (y : G) = (z : G) at he
  have hyV : y ∈ V.subgroupOf Y := by
    change (y : G) ∈ V
    rw [he]
    exact hzV
  change ¬ Function.Injective ((QuotientGroup.mk' (pCore 2 Y)).comp
    (V.subgroupOf Y).subtype)
  intro hi
  have hyq : QuotientGroup.mk' (pCore 2 Y) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  have hyone : (⟨y,hyV⟩ : V.subgroupOf Y) = 1 := hi (by simpa using hyq)
  exact hz1 (Subtype.ext (he.symm.trans (congrArg (fun a : V.subgroupOf Y => (a.val : G)) hyone)))

/-- The quotient strictly reduces the order of the actual original omega-span. -/
theorem Input.local_omega_span_quotient_card_lt
    {T : Sylow 2 G} {L W H Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    Nat.card ((V.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) < Nat.card V := by
  let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hVY : V ≤ Y := (LocalOmega.span_elementary_le_sylow T L
    (h.qtke.evenCharacteristic T) h.maximal_local.1 h.sylow_normalizes).2.trans
      (hH.1.1.2.trans hY.2)
  change Nat.card ((V.subgroupOf Y).map q) < Nat.card V
  by_contra hc
  have hi := (q.subgroupMap_surjective (V.subgroupOf Y)).bijective_of_nat_card_le
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hVY).toEquiv]; exact Nat.le_of_not_gt hc)
  apply Input.local_omega_span_quotient_not_injective h hH hY
  intro x y he
  exact hi.1 (Subtype.ext he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
