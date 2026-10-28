module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSeedSelection
public import Theory.Representation.ConjugateSpanFixedFree

/-!
# The original omega-span from a stationary natural moved layer

Outside centralization makes the full reduced subgroup fixed-free. The
omega-span inherits this property. Its seed is fixed by a Sylow subgroup
of L, so odd-index averaging makes the span equal to its own commutator.
It is consequently a nonzero invariant subgroup of the natural moved
layer and equals that layer by irreducibility. The resulting natural
coordinates give the literal quotient model with the original actor.

No first-cohomology vanishing for the natural module is asserted or used.
Source: Aschbacher--Smith 6.1.4--5, printed pp.664--666, and A.1.39.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem natural_fixed_quotient_of_full_model
    {L B : Subgroup G} {n : ℕ} (hm : IsNaturalModule L B n)
    (hc : B ⊓ centralizer (L : Set G) = ⊥) : IsNaturalFixedQuotient L B n := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hm
  let := ZMod.algebra F 2
  have hn : L ≤ normalizer (B : Set G) :=
    (show IsConjugationModel L B
      ((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)) from ⟨e,f,hf⟩).normalizes
  let m : ConjugationQuotientModel L B
      ((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)) := {
    normalizes := hn
    actor := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    quotient := f.toMonoidHom
    surjective := f.surjective
    kernel := by
      ext b
      constructor
      · intro hb
        have he : b = 1 := f.injective (hb.trans f.map_one.symm)
        subst b
        exact one_mem _
      · intro hb
        have he : b = 1 := Subtype.ext (hc.le ⟨b.property,hb⟩)
        exact he ▸ f.map_one
    equivariant := by
      intro l b
      change f (B.normalizerMonoidHom ⟨l,hn l.property⟩ b) =
        Multiplicative.ofAdd (specialLinearNatural 2
          (e (QuotientGroup.mk' (pCore 2 L) l)) (f b).toAdd)
      apply f.symm.injective
      rw [f.symm_apply_apply]
      apply Subtype.ext
      exact (hf l b).symm }
  exact ⟨F,inferInstance,inferInstance,inferInstance,hF,e,m,rfl⟩

private theorem RankOneGeneric.Input.stationary_omega_eq_natural_layer
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : RankOneGeneric.Input KnownSimple.IsKnownSimple T L W n)
    (hZW : omegaOneCenterAmbient (T : Subgroup G) ≤ W)
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hm : IsNaturalModule L (layer L W) n) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L = layer L W := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside h.outside
  have hc := h.reduced_fixed_eq_bot_of_outside_centralizes hH
    (h.omega_centralizes_of_thompson_centralizes hH hj)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z L
  have hUW : U ≤ W := conjugateSpanBy_le hZW
    (le_sup_left.trans (reduced_normalizes h.reduced))
  let := h.reduced.2.1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUW
  have hcU : U ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hUW).trans_eq hc)
  obtain ⟨P,hP⟩ := RankOneGeneric.exists_sylow_component h.sylow_normalizes
  have hSF : Z ≤ centralizer (((P : Subgroup L).map L.subtype) : Set G) := by
    intro z hz p hp
    have hpT : p ∈ (T : Subgroup G) := (hP ▸ hp).1
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 p hpT
  have hmove : ⁅U,L⁆ = U :=
    conjugateSpan_commutator_eq_of_fixed_free Z L P hSF hcU
  have hUL : U ≤ layer L W := hmove.symm.le.trans (commutator_mono hUW le_rfl)
  have hW0 : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hW0 h.reduced_le_sylow
      (le_sup_right.trans (reduced_normalizes h.reduced)))
  have hzZ : (z:G) ∈ Z := (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨h.reduced_le_sylow z.property.1,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (z:G) z.property.1,z.property.2.2⟩
  have hU0 : U ≠ ⊥ := by
    intro he
    exact hz1 (Subtype.ext (he.le (le_conjugateSpanBy Z L hzZ)))
  exact (hm.invariant_subgroup U hUL (le_normalizer_conjugateSpanBy Z L)).resolve_left hU0

namespace Hypothesis611
variable {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- In the stationary full-reduced branch, a natural moved layer gives the
exact natural fixed quotient on the original omega-span. -/
theorem omega_natural_fixed_quotient_of_stationary_natural_enlargement
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G))
    (hm : IsNaturalModule L (layer L (reducedSubgroup (L ⊔ (T : Subgroup G)))) n) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  let hR := h.reduced_enlargement
  let hi := hR.rankOneInput hout
  have he := hi.stationary_omega_eq_natural_layer h.omega_le_reduced_enlargement hj hm
  have hnat : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := he.symm ▸ hm
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hi.outside
  have hc := hi.reduced_fixed_eq_bot_of_outside_centralizes hH
    (hi.omega_centralizes_of_thompson_centralizes hH hj)
  have hUW := conjugateSpanBy_le h.omega_le_reduced_enlargement
    (le_sup_left.trans (reduced_normalizes hR.V_mem))
  exact natural_fixed_quotient_of_full_model hnat
    (bot_unique ((inf_le_inf_right _ hUW).trans_eq hc))

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
