module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoBorelSource
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme
public import Theory.SpecificGroups.SymplecticFour.Binary.DerivedFlagGeometry
public import Theory.GroupTheory.PCorePreimageCentralizer

/-!
# The field-two derived symplectic Borel on original source data

The two A6 parabolics have characteristic two and exhaust proper
Sylow overgroups. Source 2.5.1 forces their interchange, so M∩D is
exactly the component Sylow. The actual six-letter polar equivalence
then gives the literal Sp4(2)' endpoint, for every field of order two.
This does not replace Sp4(2)' by the nonsimple full Sp4(2).

Source: Aschbacher--Smith 2.5.2(2), printed p.551.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}
theorem alternating_six_aligned_borel_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (e : D ≃* A6)
    (hU : ((S : Subgroup H).subgroupOf D).map e.toMonoidHom = a6Borel) :
    ((M.subgroupOf H).subgroupOf D) = (S : Subgroup H).subgroupOf D ∧
      ∃ s : normalizer (D : Set H), (s : H) ∈ S ∧
        (a6DuadStabilizer.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          a6SynthemeStabilizer.comap e.toMonoidHom ∧
        (a6SynthemeStabilizer.comap e.toMonoidHom).map (D.normalizerMonoidHom s).toMonoidHom =
          a6DuadStabilizer.comap e.toMonoidHom := by
  let f := e.toMonoidHom
  let : f.range.Normal := by rw [f.range_eq_top_of_surjective e.surjective]; infer_instance
  have hk : IsPGroup 2 f.ker := by rw [show f.ker = ⊥ from f.ker_eq_bot e.injective]; exact IsPGroup.of_bot
  let B := a6Borel.comap f
  let P := a6DuadStabilizer.comap f
  let Q := a6SynthemeStabilizer.comap f
  have hpre : a6Borel.comap f = (S : Subgroup H).subgroupOf D := by
    rw [← hU, Subgroup.comap_map_eq_self_of_injective e.injective]
  have hNB : normalizer (a6Borel : Set A6) = a6Borel :=
    Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry.normalizer_sylow
      (MulEquiv.refl A6) a6BorelSylow
  have hB : B = normalizer ((S : Subgroup H).subgroupOf D : Set D) := by
    rw [show B = a6Borel.comap f from rfl, ← hNB,
      comap_normalizer_eq_of_surjective _ e.surjective, hpre]
  have hcB : centralizer (pCore 2 a6Borel : Set a6Borel) ≤ pCore 2 a6Borel := by
    have hc : pCore 2 a6Borel = ⊤ := top_unique (le_sSup
      ⟨inferInstance, a6BorelSylow.isPGroup'.to_subgroup ⊤⟩)
    rw [hc]
    exact le_top
  have hBc := f.centralizer_pCore_comap_of_normal_range hk _ hcB
  have hPc := f.centralizer_pCore_comap_of_normal_range hk _ a6DuadCore_centralizer.le
  have hQc := f.centralizer_pCore_comap_of_normal_range hk _ a6SynthemeCore_centralizer.le
  have hP : IsCoatom P := isCoatom_comap_of_surjective e.surjective a6DuadStabilizer_isCoatom
  have hQ : IsCoatom Q := isCoatom_comap_of_surjective e.surjective a6SynthemeStabilizer_isCoatom
  have hPQ : P ≠ Q := fun he => a6_parabolics_ne ((comap_injective e.surjective) he)
  have hinf : P ⊓ Q = B := rfl
  have hsup : P ⊔ Q = ⊤ := by
    apply (map_injective (f := f) e.injective)
    rw [Subgroup.map_sup, map_comap_eq_self_of_surjective e.surjective,
      map_comap_eq_self_of_surjective e.surjective, a6_parabolics_sup,
      map_top_of_surjective f e.surjective]
  have hcover (J : Subgroup D) (hBJ : B ≤ J) (hne : J ≠ ⊤) : J ≤ P ∨ J ≤ Q := by
    have hBJ' : a6Borel ≤ J.map f := by
      have hh := map_mono (f := f) hBJ
      rwa [map_comap_eq_self_of_surjective e.surjective] at hh
    have hj : J.map f ≠ ⊤ := by
      intro he
      apply hne
      apply map_injective (f := f) e.injective
      rw [he, map_top_of_surjective f e.surjective]
    exact (a6_overgroup_borel (J.map f) hBJ' hj).imp
      map_le_iff_le_comap.mp map_le_iff_le_comap.mp
  obtain ⟨he,hs⟩ := rank_two_intersection_eq_borel_source hH hempty S hSM D hD hout B P Q
    hB hBc hPc hQc hP hQ hPQ hinf hsup hcover
  exact ⟨he.trans hpre,hs⟩

theorem alternating_six_intersection_eq_sylow_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (e₀ : D ≃* A6) :
    ((M.subgroupOf H).subgroupOf D) = (S : Subgroup H).subgroupOf D := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  let P := R.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A6 P a6BorelSylow
  let e := e₀.trans (MulAut.conj g)
  have hU : ((S : Subgroup H).subgroupOf D).map e.toMonoidHom = a6Borel := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((R : Subgroup D).map e₀.toMonoidHom).map (MulAut.conj g).toMonoidHom = a6Borel at hh
    rw [map_map,hR] at hh
    exact hh
  exact (alternating_six_aligned_borel_source hH hempty S hSM D hD hout e hU).1

theorem symplectic_binary_derived_intersection_eq_sylow_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : D ≃* commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    ((M.subgroupOf H).subgroupOf D) = (S : Subgroup H).subgroupOf D :=
  alternating_six_intersection_eq_sylow_source hH hempty S hSM D hD hout
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
