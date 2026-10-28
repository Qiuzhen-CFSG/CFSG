module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.LinearSelection.BorelTransport
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreePrimeBorel
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.Reduction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry

/-!
# Excluding the larger-field Ree Borel

The genuine fixed-point Ree Borel has order prime to three. Sylow
conjugacy identifies every Sylow normalizer with this Borel. Transport
through the actual LocalBlockInput model equivalence and the component's
central two-kernel contradicts the rank-two subgroup Y₊ in the original
Borel. No model-order or simplicity certificate is required.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), family
selection in the final proof of 15.3.35, printed p.1139. The concrete Ree
Borel calculation is also used in the proof of Proposition 1.3.4, p.511.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection
open Chapter1.Section02.LocalModels

variable {D : Type*} [Group D] [Finite D]

/-- Every Sylow normalizer in the genuine Ree carrier has order prime to three. -/
theorem three_not_dvd_normalizer_of_ree {m : ℕ}
    (hmodel : IsReeF4At D m) (P : Sylow 2 D) :
    ¬ 3 ∣ Nat.card (normalizer (P : Set D)) := by
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  let e' := e.trans d.modelEquiv
  let Q := P.mapSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨g, hg⟩ := ReeF4.Parabolics.ThreeSylowContainment.exists_conjugate_eq_unipotent Q
  let a := e'.trans (MulAut.conj g)
  have hP : (P : Subgroup D).map a.toMonoidHom = ReeF4.Parabolics.unipotent m := by
    change (P : Subgroup D).map ((MulAut.conj g).toMonoidHom.comp e'.toMonoidHom) = _
    rw [← map_map]
    exact hg
  have hN : (normalizer (P : Set D)).map a.toMonoidHom = ReeF4.Parabolics.borel m := by
    calc
      _ = normalizer (((P : Subgroup D).map a.toMonoidHom) : Set (ReeF4.Model m)) :=
        map_equiv_normalizer_eq (P : Subgroup D) a
      _ = _ := by rw [hP, ReeF4.Parabolics.unipotent_normalizer_eq_borel]
  have hc : Nat.card (ReeF4.Parabolics.borel m) = Nat.card (normalizer (P : Set D)) := by
    rw [← hN, card_map_of_injective a.injective]
  rw [← hc]
  apply Nat.prime_three.coprime_iff_not_dvd.mp
  exact ReeF4.Parabolics.ThreePrimeBorel.borel_coprime_three_of_torus m
    (ReeF4.Parabolics.splitTorus_eq_diagonalTorus m).le

variable {G : Type*} [Group G] [Finite G]

/-- The Ree family cannot contain the source rank-two actor in its Borel. -/
theorem not_ree_component
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B) {m : ℕ} :
    ¬ IsReeF4At (componentImage I L L) m := by
  intro hmodel
  exact no_three_free_component_borel I L M Yplus S B c hB hYB
    (three_not_dvd_normalizer_of_ree hmodel)
end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection
