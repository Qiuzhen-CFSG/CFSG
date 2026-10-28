module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.Defs


/-!
# Faithful replacement of the cyclic section

Subgroups with the same induced automizer image and faithful action are
isomorphic through that image, with exactly the same conjugation on V.
This transports every clause of `RegularCyclicSection`, including regularity
and relative normality. Complements to the same centralizer have the same
induced image, so the lemma applies to the compatible PSL₃ root torus.
Source: the choice of X in Aschbacher–Smith E.6.11(2) and E.6.25,
printed pp.249–250,255.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G]

private def sectionAction (V X : Subgroup G) (hX : X ≤ normalizer (V : Set G)) :
    X →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hX)

private theorem sectionAction_range {V X : Subgroup G}
    (hX : X ≤ normalizer (V : Set G)) :
    (sectionAction V X hX).range = inducedAutomizer V X := by
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨inclusion hX x,x.property,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x.val,hx⟩,rfl⟩

private theorem sectionAction_injective {V X : Subgroup G}
    (hX : X ≤ normalizer (V : Set G)) (hf : X ⊓ centralizer (V : Set G) = ⊥) :
    Function.Injective (sectionAction V X hX) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply Subtype.ext
  have hc : (x : G) ∈ centralizer (V : Set G) := by
    have hh : inclusion hX x ∈ V.normalizerMonoidHom.ker := by
      apply MonoidHom.mem_ker.mpr
      exact congrArg Subtype.val hx
    rwa [normalizerMonoidHom_ker] at hh
  exact mem_bot.mp (hf ▸ (show (x : G) ∈ X ⊓ centralizer (V : Set G) from ⟨x.property,hc⟩))

private theorem section_equiv {V X Y : Subgroup G}
    (hX : X ≤ normalizer (V : Set G)) (hY : Y ≤ normalizer (V : Set G))
    (hfX : X ⊓ centralizer (V : Set G) = ⊥)
    (hfY : Y ⊓ centralizer (V : Set G) = ⊥)
    (hi : inducedAutomizer V Y = inducedAutomizer V X) :
    ∃ e : Y ≃* X, ∀ (y : Y) (v : G), v ∈ V →
      (e y : G) * v * (e y : G)⁻¹ = (y : G) * v * (y : G)⁻¹ := by
  let ex := MonoidHom.ofInjective (sectionAction_injective hX hfX)
  let ey := MonoidHom.ofInjective (sectionAction_injective hY hfY)
  have hr : (sectionAction V Y hY).range = (sectionAction V X hX).range := by
    rw [sectionAction_range,sectionAction_range,hi]
  let eqr := MulEquiv.subgroupCongr hr
  let e : Y ≃* X := ey.trans (eqr.trans ex.symm)
  refine ⟨e,?_⟩
  intro y v hv
  have he : sectionAction V X hX (e y) = sectionAction V Y hY y := by
    exact congrArg Subtype.val (ex.apply_symm_apply (eqr (ey y)))
  exact congrArg (fun a : Automizer V => (a.val ⟨v,hv⟩ : G)) he

/-- Replace a faithful section by another subgroup with the same actual action image.
All regularity and relative-normality clauses are transported. -/
theorem regularCyclicSection_of_same_image {M V U X Y : Subgroup G}
    (hX : RegularCyclicSection M V U X)
    (hY : Y ≤ localNormalizer M V ⊓ centralizer (U : Set G))
    (hfY : Y ⊓ centralizer (V : Set G) = ⊥)
    (hi : inducedAutomizer V Y = inducedAutomizer V X) :
    RegularCyclicSection M V U Y := by
  have hXN : X ≤ normalizer (V : Set G) := hX.contained.trans (inf_le_left.trans inf_le_right)
  have hYN : Y ≤ normalizer (V : Set G) := hY.trans (inf_le_left.trans inf_le_right)
  obtain ⟨e,he⟩ := section_equiv hXN hYN hX.faithful hfY hi
  have hW : ⁅V,Y⁆ = ⁅V,X⁆ := by
    rw [commutator_comm V Y,commutator_comm V X]
    apply le_antisymm
    · apply commutator_le.mpr
      intro y hy v hv
      have hh : ⁅y,v⁆ = ⁅(e ⟨y,hy⟩ : G),v⁆ := by
        change y*v*y⁻¹*v⁻¹ = _
        rw [← he ⟨y,hy⟩ v hv]
        rfl
      rw [hh]
      exact commutator_mem_commutator (e ⟨y,hy⟩).property hv
    · apply commutator_le.mpr
      intro x hx v hv
      have hh := he (e.symm ⟨x,hx⟩) v hv
      simp only [e.apply_symm_apply] at hh
      have hh' : ⁅x,v⁆ = ⁅(e.symm ⟨x,hx⟩ : G),v⁆ := congrArg (· * v⁻¹) hh
      rw [hh']
      exact commutator_mem_commutator (e.symm ⟨x,hx⟩).property hv
  have hfixed : V ⊓ centralizer (Y : Set G) = V ⊓ centralizer (X : Set G) := by
    ext v
    constructor
    · rintro ⟨hv,hc⟩
      refine ⟨hv,mem_centralizer_iff.mpr ?_⟩
      intro x hx
      have hh := he (e.symm ⟨x,hx⟩) v hv
      simp only [e.apply_symm_apply] at hh
      have hc' := mem_centralizer_iff.mp hc _ (e.symm ⟨x,hx⟩).property
      rw [hc',mul_inv_cancel_right] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · rintro ⟨hv,hc⟩
      refine ⟨hv,mem_centralizer_iff.mpr ?_⟩
      intro y hy
      have hh := he ⟨y,hy⟩ v hv
      have hc' := mem_centralizer_iff.mp hc _ (e ⟨y,hy⟩).property
      rw [hc',mul_inv_cancel_right] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
  refine { contained := hY
           cyclic := by let _ := hX.cyclic; exact isCyclic_of_injective e.toMonoidHom e.injective
           card_eq := (Nat.card_congr e.toEquiv).trans hX.card_eq
           faithful := hfY
           fixed := hfixed.trans hX.fixed
           spanning := hW ▸ hX.spanning
           disjoint := hW ▸ hX.disjoint
           regular := ?_
           normal_image := hi ▸ hX.normal_image }
  intro v hv hvne w hw hwne
  have hvV : v ∈ V := le_normalizer_iff_commutator_le_left.mp hYN hv
  obtain ⟨x,hx,hunique⟩ := hX.regular v (hW ▸ hv) hvne w (hW ▸ hw) hwne
  refine ⟨e.symm x,?_,?_⟩
  · dsimp only
    rw [← he (e.symm x) v hvV,e.apply_symm_apply]
    exact hx
  · intro y hy
    apply e.injective
    rw [e.apply_symm_apply]
    apply hunique
    rw [he y v hvV]
    exact hy

private theorem inducedAutomizer_centralizing_sup {V C X : Subgroup G}
    (hC : C ≤ centralizer (V : Set G)) (hX : X ≤ normalizer (V : Set G)) :
    inducedAutomizer V (C ⊔ X) = inducedAutomizer V X := by
  let N := normalizer (V : Set G)
  have hCN : C ≤ N := hC.trans (centralizer_le_normalizer _)
  have hsup : (C ⊔ X).subgroupOf N = C.subgroupOf N ⊔ X.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le (sup_le hCN hX),Subgroup.map_sup,
      map_subgroupOf_eq_of_le hCN,map_subgroupOf_eq_of_le hX]
  change ((C ⊔ X).subgroupOf N).map V.normalizerMonoidHom.rangeRestrict = _
  rw [hsup,Subgroup.map_sup]
  have hbot : (C.subgroupOf N).map V.normalizerMonoidHom.rangeRestrict = ⊥ :=
    (inducedAutomizer_eq_bot_iff hCN).mpr hC
  rw [hbot,bot_sup_eq]
  rfl

/-- Two complements to the same centralizer have identical induced actions. -/
theorem inducedAutomizer_eq_of_centralizing_complements {V C B X Y : Subgroup G}
    (hC : C ≤ centralizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (hX : C ⊔ X = B) (hY : C ⊔ Y = B) :
    inducedAutomizer V Y = inducedAutomizer V X := by
  have hXN : X ≤ normalizer (V : Set G) := (le_sup_right.trans hX.le).trans hB
  have hYN : Y ≤ normalizer (V : Set G) := (le_sup_right.trans hY.le).trans hB
  rw [← inducedAutomizer_centralizing_sup hC hYN,hY,← hX,
    inducedAutomizer_centralizing_sup hC hXN]

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
