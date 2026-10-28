module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer

/-!
# Assembly for local core quotients in a proper Held extension

The marked faithful action identifies a proper extension with Aut(He) using
the proved full-normalizer bound and automorphism realization. A cover by conjugates
of the two literal normalizers then gives an actual local isomorphism,
using the source's maximality subject to F*=O₂. The first normalizer's order
excludes nine; the second has two-core quotient of order 72.

`profile_of_realization` discharges the concrete coverage, characteristic-two,
quotient-order and full-normalizer-bound inputs of the retained conditional
assembly. Only realization of abstract automorphisms remains explicit, with its
discharge owned by the source Held-exclusion assembly. No rank-two shadow or
desired source contradiction is an input to the intrinsic profile. The final
application uses the literal local subgroup in I/C_I(L) from 15.3.41(2).

Source: Aschbacher--Smith 15.3.41--42, printed p.1138, and GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
variable {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* Held.He)

include e in
/-- Conditional assembly of the proper-extension profile from the exact two
normalizers. Coverage, characteristic two and the two numerical calculations
are still model obligations, as is the full-normalizer bound. This theorem
is not the completed source inspection or the unconditional requested profile. -/
theorem profile_of_normalizer_calculations [Finite H]
    (hc : centralizer (K : Set H) = ⊥) (hproper : K ≠ ⊤)
    (P : Sylow 2 H) (N : Subgroup H)
    (hlocal : IsTwoLocal N) (hPN : (P : Subgroup H) ≤ N)
    (hF : generalizedFitting N = pCore 2 N)
    (hmax : ∀ J : Subgroup H, N ≤ J → generalizedFitting J = pCore 2 J → J = N)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hcharacteristic : ∀ i : Bool, generalizedFitting (candidate i) = pCore 2 (candidate i))
    (hcover : ∀ (T : Sylow 2 (MulAut Held.He)) (D : Subgroup (MulAut Held.He)),
      IsTwoLocal D → (T : Subgroup (MulAut Held.He)) ≤ D →
      generalizedFitting D = pCore 2 D →
      ∃ (i : Bool) (g : MulAut Held.He), D ≤ (candidate i).map (MulAut.conj g).toMonoidHom)
    (hsmall : ¬ 9 ∣ Nat.card (candidate false))
    (hseventyTwo : Nat.card (candidate true ⧸ pCore 2 (candidate true)) = 72) :
    (¬ 9 ∣ Nat.card (pCore 3 (N ⧸ pCore 2 N))) ∨ Nat.card (N ⧸ pCore 2 N) = 72 := by
  let f := autEquivOfInnerInterval K e hc hproper (inner_interval_of_normalizer_bound hreal hbound)
  obtain ⟨i, ⟨a⟩⟩ := local_equiv_of_cover f candidate P N hlocal hPN hF hmax
    hcharacteristic hcover
  cases i
  · left
    rw [threeCore_quotient_card_eq a]
    intro hnine
    exact hsmall (hnine.trans ((card_subgroup_dvd_card _).trans (card_quotient_dvd_card _)))
  · right
    exact (Nat.card_congr (coreQuotientEquiv a).toEquiv).trans hseventyTwo

include e in
/-- The intrinsic local quotient profile of a proper Held extension. All local
model calculations and the full-normalizer quotient bound are discharged.
Automorphism realization is the sole independent model premise.

The faithful marked action suffices: the source's additional simplicity,
perfectness, ambient generalized-Fitting equality and Sylow-generation
hypotheses are unnecessary for this stronger local statement. -/
theorem profile_of_realization [Finite H]
    (hc : centralizer (K : Set H) = ⊥) (hproper : K ≠ ⊤)
    (P : Sylow 2 H) (N : Subgroup H)
    (hlocal : IsTwoLocal N) (hPN : (P : Subgroup H) ≤ N)
    (hF : generalizedFitting N = pCore 2 N)
    (hmax : ∀ J : Subgroup H, N ≤ J → generalizedFitting J = pCore 2 J → J = N)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    (¬ 9 ∣ Nat.card (pCore 3 (N ⧸ pCore 2 N))) ∨ Nat.card (N ⧸ pCore 2 N) = 72 := by
  have hbound := Held.permutationNormalizerQuotient_card_le_two
  obtain ⟨hcharacteristic, hsmall, hseventyTwo⟩ := normalizer_calculations hreal hbound
  exact profile_of_normalizer_calculations K e hc hproper P N hlocal hPN hF hmax
    hreal hbound hcharacteristic (local_cover hreal hbound) hsmall hseventyTwo

/-- Application to the actual local subgroup M_I⁺ in I/C_I(L). This supplies
the proper-extension branch of the model inspection in 15.3.42, to be combined
with `componentLocal_restrictions` by the Held-exclusion assembly owner.
Only the separately owned automorphism-realization premise remains. -/
theorem componentLocal_profile_of_realization
    {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
    [(L.subgroupOf I).Normal] (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Held.He) (hproper : componentImage I L L ≠ ⊤)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    (¬ 9 ∣ Nat.card (pCore 3 ((componentImage I L M) ⧸ pCore 2 (componentImage I L M)))) ∨
      Nat.card ((componentImage I L M) ⧸ pCore 2 (componentImage I L M)) = 72 := by
  obtain ⟨P, hP⟩ := d.quotient_local.sylow
  exact profile_of_realization (componentImage I L L) (componentModel d e)
    (componentImage_faithful d) hproper P (componentImage I L M)
    d.quotient_local.twoLocal (hP.symm ▸ d.quotient_local.sylow_le)
    d.quotient_local.characteristicTwo d.quotient_local.maximal hreal

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
