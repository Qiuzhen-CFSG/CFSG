module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Lifts

/-!
# Normally generated lifts of the exceptional factor

Lift the factor through the two-residual of its full automizer preimage,
then normally generate X inside that residual. The image is the prescribed
factor when its cyclic image normally generates it. If the residual lift
normalizes a containing local component, the generated lift lies in it.
No oddness or two-perfectness of the full preimage is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
E.6.25, printed pp.255–256 (PDF pp.266–267).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
variable {G : Type*} [Group G]

theorem le_automizerPreimage {V X : Subgroup G} {B : Subgroup (Automizer V)}
    (hXN : X ≤ normalizer (V : Set G)) (hXB : inducedAutomizer V X ≤ B) :
    X ≤ automizerPreimage V B := by
  intro x hx
  exact ⟨⟨x, hXN hx⟩, hXB ⟨⟨x, hXN hx⟩, hx, rfl⟩, rfl⟩

theorem le_residualLift_of_odd {V X : Subgroup G} {B : Subgroup (Automizer V)}
    (hXN : X ≤ normalizer (V : Set G)) (hXB : inducedAutomizer V X ≤ B)
    (ho : Odd (Nat.card X)) : X ≤ residualLift V B := by
  have hXP := le_automizerPreimage hXN hXB
  intro x hx
  refine ⟨⟨x, hXP hx⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have he : orderOf (⟨x, hXP hx⟩ : automizerPreimage V B) = orderOf (⟨x, hx⟩ : X) := by
    simp only [Subgroup.orderOf_mk]
  rw [he]
  exact ho.coprime_two_left.of_dvd_right (orderOf_dvd_natCard _)

/-- The normal closure is taken inside the two-perfect lift, not its full preimage. -/
def generatedFactorLift (V X : Subgroup G) (B : Subgroup (Automizer V)) : Subgroup G :=
  (normalClosure (X.subgroupOf (residualLift V B) : Set (residualLift V B))).map
    (residualLift V B).subtype

theorem generatedFactorLift_le (V X : Subgroup G) (B : Subgroup (Automizer V)) :
    generatedFactorLift V X B ≤ residualLift V B := map_subtype_le _

theorem generatedFactorLift_le_of_normalizes {V X L : Subgroup G}
    {B : Subgroup (Automizer V)} (hXL : X ≤ L)
    (hN : residualLift V B ≤ normalizer (L : Set G)) :
    generatedFactorLift V X B ≤ L := by
  let P := residualLift V B
  let _ : (L.subgroupOf P).Normal := by
    refine ⟨?_⟩
    intro n hn g
    exact (mem_normalizer_iff.mp (hN g.property) n).mp hn
  rintro x ⟨y, hy, rfl⟩
  exact normalClosure_le_normal (N := L.subgroupOf P) (fun z hz => hXL hz) hy

/-- The actual action of a residual lift on V, with codomain the chosen factor. -/
def residualFactorAction (V : Subgroup G) (B : Subgroup (Automizer V)) :
    residualLift V B →* B :=
  (V.normalizerMonoidHom.rangeRestrict.comp (inclusion (residualLift_le V B))).codRestrict B
    (by
      intro x
      obtain ⟨n, hn, he⟩ := residualLift_le_preimage V B x.property
      change V.normalizerMonoidHom.rangeRestrict ⟨x, residualLift_le V B x.property⟩ ∈ B
      have he' : n = ⟨x, residualLift_le V B x.property⟩ := Subtype.ext he
      exact he' ▸ hn)

variable [Finite G]

theorem residualFactorAction_surjective (V : Subgroup G) (B : Subgroup (Automizer V))
    (ho : Odd (Nat.card B)) : Function.Surjective (residualFactorAction V B) := by
  intro b
  have hb : (b : Automizer V) ∈ inducedAutomizer V (residualLift V B) := by
    rw [inducedAutomizer_residualLift V B ho]
    exact b.property
  obtain ⟨n, hn, he⟩ := hb
  refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
  exact he

theorem generatedFactorLift_image {V X : Subgroup G} {B : Subgroup (Automizer V)}
    (hXN : X ≤ normalizer (V : Set G)) (hXB : inducedAutomizer V X ≤ B)
    (hoX : Odd (Nat.card X)) (hoB : Odd (Nat.card B))
    (hgen : normalClosure ((inducedAutomizer V X).subgroupOf B : Set B) = ⊤) :
    inducedAutomizer V (generatedFactorLift V X B) = B := by
  let P := residualLift V B
  let f := residualFactorAction V B
  have hXP := le_residualLift_of_odd hXN hXB hoX
  have hmap : (X.subgroupOf P).map f = (inducedAutomizer V X).subgroupOf B := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, residualLift_le V B x.property⟩, hx, rfl⟩
    · rintro ⟨n, hn, he⟩
      exact ⟨⟨n, hXP hn⟩, hn, Subtype.ext he⟩
  have hsur : (normalClosure (X.subgroupOf P : Set P)).map f = ⊤ := by
    rw [map_normalClosure _ f (residualFactorAction_surjective V B hoB)]
    change normalClosure ((X.subgroupOf P).map f : Set B) = ⊤
    rw [hmap, hgen]
  apply le_antisymm
  · apply le_trans (Subgroup.map_mono (Subgroup.comap_mono (generatedFactorLift_le V X B)))
    exact (inducedAutomizer_residualLift V B hoB).le
  · intro b hb
    obtain ⟨x, hx, he⟩ := hsur.symm ▸ (mem_top (⟨b, hb⟩ : B))
    refine ⟨⟨x, residualLift_le V B x.property⟩, ⟨x, hx, rfl⟩, ?_⟩
    exact congrArg Subtype.val he
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
