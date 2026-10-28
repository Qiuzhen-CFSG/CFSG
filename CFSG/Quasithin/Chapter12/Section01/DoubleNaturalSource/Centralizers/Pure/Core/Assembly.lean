module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Pairs
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Assembly
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic

/-!
# Pure-point closure after component exclusion

The marked action supplies the core commutator bound. Self-centralization of
the point core puts the natural summand and dual hyperplane into it, and the
two-conjugate argument then puts the whole doubled module into the core.
This discharges all local core callbacks in the earlier closure application.

The remaining source obligations are the characteristic-two conclusion from
component exclusion and the dimension-four marked Sylow theorem. In dimension
five the permitted positive globalW premise already supplies the Sylow and
order data. The final assembly owner is `qt-d-double-natural-pure-fusion`.
Source: Aschbacher--Smith 12.1.4--6, printed pp.790--792.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- H.9 and the actual ambient Sylows give the natural-section bound. -/
theorem doubleNatural_pure_core_commutator_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.PurePointSylows →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        ⁅B.naturalSummand, B.purePointCore w⁆ ≤ zpowers (w : G) := by
  let := D.doubledOrbit_elementary h
  intro S hs w hw hp
  exact S.purePointCore_natural_commutator
    (D.doubledOrbit_normalizer_eq h B.orbit_eq) hs w hw hp

/-- The complete local core argument, conditional on the remaining source
component exclusion for the original point centralizers. -/
theorem doubleNatural_pure_coreControl_of_characteristicTwo_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.PurePointSylows → B.NonsingularCentralizers →
      (∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        generalizedFitting (centralizer ({(w : G)} : Set G)) =
          pCore 2 (centralizer ({(w : G)} : Set G))) → B.PureCoreControl := by
  let := D.doubledOrbit_elementary h
  intro S hs hns hc
  have hn := D.doubledOrbit_normalizer_eq h B.orbit_eq
  exact ⟨fun w hw hp => S.pure_orbit_le_core_of_characteristicTwo hn hs hns w hw hp
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (hc w hw hp)),
    S.purePointCore_natural_commutator hn hs⟩

/-- The three original conclusions from centralizer orders, ambient Sylows
and the component exclusion; no local order, Sylow or core proof is claimed. -/
theorem doubleNatural_pure_conclusions_of_characteristicTwo_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.CentralizerOrders → B.PurePointSylows →
      B.NonsingularCentralizers →
      (∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        generalizedFitting (centralizer ({(w : G)} : Set G)) =
          pCore 2 (centralizer ({(w : G)} : Set G))) →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S ho hs hns hc
  exact D.doubleNatural_pure_conclusions_of_orders_and_core_of_many h hmany B S ho hs
    (D.doubleNatural_pure_coreControl_of_characteristicTwo_of_many h hmany B S hs hns hc)

/-- For dimension five, the only additional premise here is the original
component-exclusion conclusion at each pure point. -/
theorem doubleNatural_five_pure_conclusions_of_characteristicTwo_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      (∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        generalizedFitting (centralizer ({(w : G)} : Set G)) =
          pCore 2 (centralizer ({(w : G)} : Set G))) →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hns hc
  obtain ⟨ho,hs,_⟩ := D.doubleNatural_five_pure_orders_sylows_fusion_of_many h hmany B hW S hns
  exact D.doubleNatural_pure_conclusions_of_characteristicTwo_of_many h hmany B S ho hs hns hc

/-- The 12.1.6 component exclusion is needed at only one nonidentity natural
point; H.9 transports its intrinsic characteristic-two equality to every pure point. -/
theorem doubleNatural_five_pure_conclusions_of_one_characteristicTwo_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      ∀ v : componentOrbit V (T : Subgroup G), v ≠ 1 →
        (B.coordinates v).toAdd.2 = 0 →
        generalizedFitting (centralizer ({(v : G)} : Set G)) =
          pCore 2 (centralizer ({(v : G)} : Set G)) →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hns v hv hpv hc
  apply D.doubleNatural_five_pure_conclusions_of_characteristicTwo_of_many h hmany B hW S hns
  intro w hw hpw
  obtain ⟨m,_,he⟩ := (S.ambient_orbit_iff v w hv hw).mpr
    (Or.inl ⟨⟨hv,Or.inl hpv⟩,⟨hw,Or.inl hpw⟩⟩)
  have hmap : (centralizer ({(v : G)} : Set G)).map (MulAut.conj m).toMonoidHom =
      centralizer ({(w : G)} : Set G) := by
    rw [map_centralizer_singleton,he]
  let e := ((MulAut.conj m).subgroupMap (centralizer ({(v : G)} : Set G))).trans
    (MulEquiv.subgroupCongr hmap)
  apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
