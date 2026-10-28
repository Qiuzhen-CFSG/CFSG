module

public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.GroupTheory.CharacteristicTwoLocalCover

/-!
# Faithful reduction of a proper Held extension

Conjugation on the relatively normal Held component gives a faithful marked
action. Its component image is exactly Inn(He), and properness makes its
range a strict overgroup of Inn(He). Once the full normalizer quotient is
bounded by two and all automorphisms are realized there, subgroup indices
force that range to be Aut(He), giving a genuine ambient equivalence.

The numerical bound is an explicit, independent obligation here. This
module does not assert an automorphism classification or a local catalogue.
Source: GLS3 Table 5.3p; Aschbacher--Smith 15.3.41--42, printed p.1138.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile

variable {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* Held.He)

/-- The ambient action on the relatively normal component, in Held coordinates. -/
noncomputable def markedAction : H →* MulAut Held.He :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

/-- Trivial component centralizer makes the marked action faithful. -/
theorem markedAction_injective (hc : centralizer (K : Set H) = ⊥) :
    Function.Injective (markedAction K e) :=
  (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)

/-- On the component itself, the marked action is the actual inner action. -/
theorem markedAction_inner (x : K) :
    markedAction K e x = MulAut.conj (e x) := by
  change MulAut.congr e (MulAut.conjNormal (x : H)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

/-- The component image is the whole inner automorphism subgroup. -/
theorem markedAction_map_component :
    K.map (markedAction K e) = MulAut.innerSubgroup Held.He := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e ⟨x, hx⟩, (markedAction_inner K e ⟨x, hx⟩).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, (e.symm x).property,
      (markedAction_inner K e (e.symm x)).trans (by rw [e.apply_symm_apply])⟩

/-- Faithfulness detects the component as precisely the elements acting by inner automorphisms. -/
theorem markedAction_comap_inner (hc : centralizer (K : Set H) = ⊥) :
    (MulAut.innerSubgroup Held.He).comap (markedAction K e) = K := by
  rw [← markedAction_map_component K e, Subgroup.comap_map_eq,
    (MonoidHom.ker_eq_bot_iff _).mpr (markedAction_injective K e hc), sup_bot_eq]

/-- A proper component gives a strict overgroup of the inner automorphisms. -/
theorem inner_lt_markedAction_range (hc : centralizer (K : Set H) = ⊥)
    (hproper : K ≠ ⊤) :
    MulAut.innerSubgroup Held.He < (markedAction K e).range := by
  have hle : MulAut.innerSubgroup Held.He ≤ (markedAction K e).range := by
    rw [← markedAction_map_component K e]
    exact Subgroup.map_le_range _ _
  refine lt_of_le_of_ne hle ?_
  intro he
  have he' := congrArg (Subgroup.comap (markedAction K e)) he
  rw [markedAction_comap_inner K e hc, MonoidHom.comap_range_self] at he'
  exact hproper he'

/-- Collapse of the actual inner-automorphism interval makes the action onto. -/
theorem markedAction_surjective_of_inner_interval
    (hc : centralizer (K : Set H) = ⊥) (hproper : K ≠ ⊤)
    (hinterval : ∀ A : Subgroup (MulAut Held.He),
      MulAut.innerSubgroup Held.He < A → A = ⊤) :
    Function.Surjective (markedAction K e) :=
  MonoidHom.range_eq_top.mp
    (hinterval _ (inner_lt_markedAction_range K e hc hproper))

/-- The compatible ambient isomorphism obtained from the faithful marked action. -/
noncomputable def autEquivOfInnerInterval
    (hc : centralizer (K : Set H) = ⊥) (hproper : K ≠ ⊤)
    (hinterval : ∀ A : Subgroup (MulAut Held.He),
      MulAut.innerSubgroup Held.He < A → A = ⊤) : H ≃* MulAut Held.He :=
  MulEquiv.ofBijective (markedAction K e)
    ⟨markedAction_injective K e hc,
      markedAction_surjective_of_inner_interval K e hc hproper hinterval⟩

/-- A proved full permutation-normalizer bound, together with realization,
collapses the interval above the inner automorphisms. The bound remains
explicit here until the existing normalizer-calculation owner supplies it. -/
theorem inner_interval_of_normalizer_bound
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (A : Subgroup (MulAut Held.He)) (hA : MulAut.innerSubgroup Held.He < A) : A = ⊤ := by
  have hindex : (MulAut.innerSubgroup Held.He).index ≤ 2 :=
    (Nat.card_le_card_of_surjective _
      (normalizerOuterAction_surjective Held.permutationGroup hreal)).trans hbound
  have hlt := Subgroup.index_strictAnti hA
  have hpos : 0 < A.index := Nat.pos_of_ne_zero A.index_ne_zero_of_finite
  exact Subgroup.index_eq_one.mp (by omega)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
