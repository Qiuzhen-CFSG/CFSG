module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoFusion
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Control of the common involution centralizer

The long core orbit has twelve elements, so its stabilizer in the centralizer
of `z`, of order 192, has order sixteen. The extraspecial core already supplies
at least sixteen elements commuting with `t`. Equality follows, giving the
source identity `C_H(t) = C_Q(t)` without a model of either full centralizer.
The orbit profile remains an explicit input supplied by the census producer.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 2.7 and the opening of Lemma 4.2.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
variable {G : Type*} [Group G] [Finite G] {z t u : G}
/-- Orbit-stabilizer on the twelve-element core orbit computes the
common centralizer in its literal ambient position. -/
public theorem commonCentralizer_card_of_orbits (h : Hypotheses z) (d : FusionEightData z) (o : Census.OrbitData z u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Nat.card (Centralizer z ⊓ Centralizer t : Subgroup G) = 16 := by
  classical
  let H := Centralizer z
  let action : H →* MulAut G := MulAut.conj.comp H.subtype
  let : MulAction H G := (MulDistribMulAction.compHom G action).toMulAction
  have horbit : MulAction.orbit H t =
      {x : G | x ∈ coreInG z ∧ orderOf x = 2 ∧ x ∉ fusionCore z} := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      change (c : G) * t * (c : G)⁻¹ ∈ coreInG z ∧ _
      have hcQ : (c : G) ∈ normalizer (coreInG z : Set G) :=
        h.normalizer_core.symm ▸ c.property
      have htc : IsConj t ((c : G) * t * (c : G)⁻¹) := isConj_iff.mpr ⟨c, rfl⟩
      have hot : orderOf ((c : G) * t * (c : G)⁻¹) = 2 :=
        ((MulAut.conj (c : G)).orderOf_eq t).trans ht
      have hne : (c : G) * t * (c : G)⁻¹ ≠ 1 := by
        intro he
        rw [he, orderOf_one] at hot
        omega
      refine ⟨(mem_normalizer_iff.mp hcQ t).mp htQ, hot, ?_⟩
      intro hf
      exact hnt ((d.fusion _ hf hne).trans htc.symm)
    · rintro ⟨hxQ, hx, hxF⟩
      have htF : t ∉ fusionCore z := fun hf =>
        hnt (d.fusion t hf (fun he => by simp [he] at ht))
      obtain ⟨c, hc⟩ := o.core_transitive ⟨t, htQ, ht, htF⟩ ⟨x, hxQ, hx, hxF⟩
      exact ⟨c, hc⟩
  have ho : Nat.card (MulAction.orbit H t) = 12 := by rw [horbit]; exact o.core_card
  let C := Centralizer z ⊓ Centralizer t
  have e : MulAction.stabilizer H t ≃ C :=
    { toFun := fun x => ⟨(x : H), x.val.property,
        mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp x.property)⟩
      invFun := fun x => ⟨⟨x, x.property.1⟩,
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card (MulAction.stabilizer H t) = Nat.card C := Nat.card_congr e
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H t)
  rw [Nat.card_prod, ho, hc, h.centralizer_card] at he
  change Nat.card C = 16
  omega

/-- The common centralizer is contained in the original core, as in the
first sentence of source 4.2. Relative and ambient centralizers are linked
by the actual core subtype map. -/
public theorem commonCentralizer_eq_core_of_orbits (h : Hypotheses z)
    (d : FusionEightData z) (o : Census.OrbitData z u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Centralizer z ⊓ Centralizer t = coreInG z ⊓ Centralizer t := by
  have hcard := commonCentralizer_card_of_orbits h d o htQ ht hnt
  have hlarge : 16 ≤ Nat.card (coreInG z ⊓ Centralizer t : Subgroup G) := by
    let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
    rw [← map_subtype_centralizer_singleton (coreInG z) ⟨t, htQ⟩,
      card_map_of_injective (coreInG z).subtype_injective]
    exact IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two
      h.coreInG_card ⟨t, htQ⟩
  exact (eq_of_le_of_card_ge (inf_le_inf_right _ (coreInG_le z))
    (hcard ▸ hlarge)).symm

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
