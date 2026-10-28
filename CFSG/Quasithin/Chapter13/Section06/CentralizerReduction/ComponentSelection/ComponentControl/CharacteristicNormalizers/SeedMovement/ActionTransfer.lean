module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.Module
public import Theory.GroupTheory.CComponent.SeedAction
/-!
# Movement through the literal quasisimple seed action

A radical supplement maps onto every quasisimple image of K₀. Apply this
to the image of K₀ in H/C_H(⟨z^H⟩). Every element of K₀ then has the same
action on z as an element of the supplement. Thus the supplement moves z
whenever K₀ does. No centralization by the radical, equality of the
replacement with K₀, or quasisimplicity of K₀/O₂(K₀) is required.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.16(2), printed p.930; the radical quotient calculation uses A.3.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement
open NonquasisimpleFactorization
variable {G : Type*} [Group G] [Finite G]

/-- Transfer movement across a radical supplement on its actual seed action. -/
theorem replacement_moves_of_quasisimple_action
    (H K K₁ : Subgroup G) (z : G) (hz : z ∈ H) (hKH : K ≤ H)
    (hgen : (solvableRadical K).map K.subtype ⊔ K₁ = K)
    (hm : ¬ K ≤ centralizer ({z} : Set G))
    (hquasi : IsQuasisimple ((K.subgroupOf H).map (actionMk (seedSpan H z hz)))) :
    ¬ K₁ ≤ centralizer ({z} : Set G) := by
  let W := seedSpan H z hz
  let q := actionMk W
  let B := K.subgroupOf H
  let Bbar := B.map q
  let e : B ≃* K := subgroupOfEquivOfLe hKH
  let f : K →* Bbar := (q.subgroupMap B).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective B).comp e.symm.surjective
  have hle : K₁ ≤ K := le_sup_right.trans_eq hgen
  let A := K₁.subgroupOf K
  have hg : solvableRadical K ⊔ A = ⊤ := by
    apply map_injective K.subtype_injective
    simpa only [Subgroup.map_sup, A, map_subgroupOf_eq_of_le hle,
      ← MonoidHom.range_eq_map, range_subtype] using hgen
  let := hquasi
  have hsur : A.map f = ⊤ := map_radical_supplement_eq_top_of_quasisimple f hf A hg
  intro hfixed
  apply hm
  intro k hk
  have hmem : f ⟨k, hk⟩ ∈ A.map f := hsur.symm ▸ mem_top _
  obtain ⟨a, ha, he⟩ := hmem
  have he' : q (⟨(a : G), hKH a.property⟩ : H) = q ⟨k, hKH hk⟩ :=
    congrArg (fun x : Bbar => (x : ActionQuotient W)) he
  have hker : (⟨k, hKH hk⟩ : H) * (⟨(a : G), hKH a.property⟩ : H)⁻¹ ∈ q.ker := by
    change q _ = 1
    rw [map_mul, map_inv, he', mul_inv_cancel]
  have hfixker : k * (a : G)⁻¹ ∈ centralizer ({z} : Set G) := by
    have hc : (⟨k, hKH hk⟩ : H) * (⟨(a : G), hKH a.property⟩ : H)⁻¹ ∈
        centralizer (W : Set H) := by simpa only [q, actionMk, QuotientGroup.ker_mk'] using hker
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((hc _ (seed_mem H z hz)).symm))
  have hafix : (a : G) ∈ centralizer ({z} : Set G) := hfixed ha
  simpa only [inv_mul_cancel_right] using (centralizer ({z} : Set G)).mul_mem hfixker hafix
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement

end
