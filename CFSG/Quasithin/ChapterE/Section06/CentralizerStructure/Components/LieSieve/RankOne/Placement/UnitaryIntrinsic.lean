module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LocalOrbit
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.UnitaryIntrinsic.RootAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.UnitaryIntrinsic.ShortPowers
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms

/-!
# Intrinsic unitary Borel facts for E.6.8

For the actual PSU₃(2^n) model, the scalar-centralizer calculation proves
that the center is trivial. The root–torus square test proves characteristic
two of the standard Borel and excludes all short subnormal subgroups of
its finite direct powers. A genuine Hermitian basis change, Sylow
conjugacy, and the supplied model equivalence transport these conclusions
to the prescribed embedded Sylow normalizer.

All intrinsic premises of `sylowBorel_le_of_intrinsic` are discharged for
the unitary branch. The field parameter is the fixed-field order 2^n;
the matrix field has order (2^n)^2 and the scalar projective quotient is
retained throughout. No placement, block exclusion, or A₃ rank bound is
assumed. Final placement using E.6.7 remains with the parent assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259); Huppert II.10.12.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryIntrinsic

private theorem exists_normalizer_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (S : Sylow 2 A) (T : Sylow 2 B) :
    Nonempty ((normalizer (S : Set A)) ≃* (normalizer (T : Set B))) := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B R T
  let a := e.trans (MulAut.conj g)
  have hmap : (S : Subgroup A).map a.toMonoidHom = (T : Subgroup B) := by
    change (S : Subgroup A).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hn : (normalizer (S : Set A)).map a.toMonoidHom = normalizer (T : Set B) := by
    calc
      _ = normalizer (((S : Subgroup A).map a.toMonoidHom) : Set B) :=
        map_normalizer_eq_of_bijective _ a.bijective
      _ = _ := by rw [hmap]; rfl
  exact ⟨((normalizer (S : Set A)).equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr hn)⟩

private theorem model_intrinsic {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hn : 0 < n) (iso : ClassicalGroup.IsPSU A 3 (2 ^ n)) (S : Sylow 2 A) :
    center A = ⊥ ∧ CFSG.Quasithin.HasCharacteristicTwo (normalizer (S : Set A)) ∧
      ∀ k, ∀ X : Subgroup (Fin k → normalizer (S : Set A)),
        X.IsSubnormal → ¬ CFSG.Quasithin.ChapterC.IsShort X := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := iso
  let _ : CharP F 2 := charP_two n hn hcard
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let J0 := FormTransport.standardForm J
  let f := e.trans (FormTransport.projectiveEquiv J C hC)
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) :=
    Finite.of_surjective _ (suProjection_surjective J0)
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J0) = ⊥ :=
    HermitianForm.EvenTwoRank.standard_center_eq_bot J0 rfl
      (exists_nonfixed J0 hn hcard hconj)
  have hA : center A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have hh : f a ∈ center (ProjectiveSpecialUnitaryMatrixGroup J0) :=
      (centerCongr f ⟨a, ha⟩).property
    rw [hz, mem_bot] at hh
    exact mem_bot.mpr (f.injective (hh.trans (map_one f).symm))
  obtain ⟨T, ht⟩ := standard_sylow_square_test J0 rfl hn hcard hconj
  obtain ⟨eN⟩ := exists_normalizer_equiv f S T
  let R := (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J0)).subgroupOf
    (normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J0)))
  let _ : R.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hp : IsPGroup 2 R := T.isPGroup'.comap_subtype
  refine ⟨hA, ?_, ?_⟩
  · exact (Theory.Quasithin.centralizer_pCore_le_iff 2 eN).mpr
      (characteristicTwo_of_square_test R hp ht)
  · exact power_noShort_transport eN (noShort_power_of_square_test R hp ht)


end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryIntrinsic

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- Every intrinsic premise needed for the unitary Borel placement branch,
with the actual embedded normalizer and all finite powers retained. -/
theorem unitary_sylowBorel_intrinsic {n : ℕ} (hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSU L 3 (2 ^ n)) (S : Sylow 2 L) :
    center L = ⊥ ∧ HasCharacteristicTwo (sylowBorel S) ∧
      ∀ k, ∀ X : Subgroup (Fin k → sylowBorel S),
        X.IsSubnormal → ¬ ChapterC.IsShort X := by
  obtain ⟨hZ, hB, hfree⟩ := UnitaryIntrinsic.model_intrinsic (by omega) iso S
  let eN := ((normalizer (S : Set L)).equivMapOfInjective
    L.subtype L.subtype_injective).symm
  exact ⟨hZ, (Theory.Quasithin.centralizer_pCore_le_iff 2 eN).mpr hB,
    UnitaryIntrinsic.power_noShort_transport eN hfree⟩

/-- The actual projective unitary component has trivial center. -/
theorem unitary_center_eq_bot {n : ℕ} (hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSU L 3 (2 ^ n)) : center L = ⊥ :=
  (unitary_sylowBorel_intrinsic hn iso (Classical.choice inferInstance)).1

/-- Characteristic two of the prescribed ambient unitary Sylow normalizer. -/
theorem unitary_sylowBorel_characteristicTwo {n : ℕ} (hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSU L 3 (2 ^ n)) (S : Sylow 2 L) :
    HasCharacteristicTwo (sylowBorel S) :=
  (unitary_sylowBorel_intrinsic hn iso S).2.1

/-- No relatively subnormal subgroup of a finite unitary Borel power is short. -/
theorem unitary_borel_power_noShort {n : ℕ} (hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSU L 3 (2 ^ n)) (S : Sylow 2 L)
    (k : ℕ) (X : Subgroup (Fin k → sylowBorel S)) (hs : X.IsSubnormal) :
    ¬ ChapterC.IsShort X :=
  (unitary_sylowBorel_intrinsic hn iso S).2.2 k X hs

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
end
