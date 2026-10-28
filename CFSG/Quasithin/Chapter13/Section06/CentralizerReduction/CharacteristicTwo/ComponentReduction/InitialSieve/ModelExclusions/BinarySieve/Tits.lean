module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.ActionTransport
public import Theory.SpecificGroups.Tits.SylowPointwiseInner

/-!
# Excluding the actual Tits endpoint

Align the pointwise-fixed Sylow subgroup with the certified Atlas Sylow
through the actual Parrott comparison. Its pointwise automorphism fixer
has only the identity and one marked inner automorphism. Faithfulness would
embed the source four-group into these two elements, a contradiction.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927. The intrinsic
calculation is also the Tits case of 16.1.6, printed p.1172.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- The exponent-one Tits carrier cannot be this component image. -/
theorem not_tits (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty (NormalizerAction.componentImage K ≃* Tits.ParrottGroup) := by
  classical
  rintro ⟨e⟩
  obtain ⟨S,hS⟩ := exists_model_sylow_fixed K a e
  obtain ⟨f,hf⟩ := Tits.RelativeSylowMarking.exists_sylow_marking
    Tits.parrottFiniteImageEquiv S
  let E := EStar s K a.a_normalizes a.z_normalizes
  let ρ : E →* MulAut Tits.Atlas1600Group :=
    ((MulAut.congr f).toMonoidHom.comp (modelAction K e)).comp E.subtype
  have hi : Function.Injective ρ := (MulAut.congr f).injective.comp
    ((modelAction_injective K hK e).comp Subtype.val_injective)
  have hc (x : E) : ρ x = 1 ∨ ρ x = MulAut.conj Tits.atlas1600R5 := by
    apply Tits.SylowPointwiseInner.atlas_fixing_standard_cases
    intro y hy
    rw [← hf] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    change f (modelAction K e x (f.symm (f z))) = f z
    rw [f.symm_apply_apply, hS x x.property z hz]
  let j : E → Bool := fun x => decide (x = 1)
  have hj : Function.Injective j := by
    intro x y he
    by_cases hx : x = 1
    · have hy : y = 1 := by simpa [j,hx] using he.symm
      exact hx.trans hy.symm
    by_cases hy : y = 1
    · have hx' : x = 1 := by simpa [j,hy] using he
      exact (hx hx').elim
    apply hi
    have hx' : ρ x ≠ 1 := fun h => hx (hi (h.trans (map_one ρ).symm))
    have hy' : ρ y ≠ 1 := fun h => hy (hi (h.trans (map_one ρ).symm))
    exact ((hc x).resolve_left hx').trans ((hc y).resolve_left hy').symm
  have hb := Nat.card_le_card_of_injective j hj
  change Nat.card (EStar s K a.a_normalizes a.z_normalizes) ≤ Nat.card Bool at hb
  rw [a.four.card_four] at hb
  norm_num at hb

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
