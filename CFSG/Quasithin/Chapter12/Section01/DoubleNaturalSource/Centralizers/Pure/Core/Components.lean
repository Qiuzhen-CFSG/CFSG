module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Odd
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Assembly
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import Theory.GroupTheory.GeneralizedFitting.InnerMovingActor

/-!
# The source component alternative at a marked pure point

The original marked ambient Sylow and a central involution of T give exactly
the 1.1.5 hypotheses for C_G(w) and C_G(z). With the odd core already proved
trivial, failure of characteristic two produces an actual component, its
commutator identity with z, and the complete model/action alternatives.

In dimension five the earlier positive globalW input supplies the marked
Sylow. The original fusion, abelian closure and intersection conclusions
therefore follow unless such a component survives. Excluding that component
and proving the dimension-four ambient Sylow remain obligations of the final
assembly owner `qt-d-double-natural-pure-fusion`; this module does not assert
the full source theorem.
Source: Aschbacher--Smith, 12.1.5--6, printed p.791, using 1.1.5--6.
-/

public section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Chapter15.Section03.Candidates.ComponentStructure
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The exact 1.1.5 setup at the original pure point and a central involution
of the original T. The overgroup here is C_G(z), as in the printed argument. -/
theorem doubleNatural_pure_component_setup_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ z : G, orderOf z = 2 → z ∈ centerIn (T : Subgroup G) →
      ∃ P : Sylow 2 (centralizer ({(w : G)} : Set G)),
        (P : Subgroup _).map (centralizer ({(w : G)} : Set G)).subtype =
          (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G) ∧
        Chapter1.Lemma115Hypotheses (centralizer ({(w : G)} : Set G)) P
          (centralizer ({z} : Set G)) z := by
  let := D.doubledOrbit_elementary h
  intro S hs w hw hp hfix z hz hzT
  obtain ⟨P,hP⟩ := hs w hw hp hfix
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  have hPT : (P : Subgroup _).map (centralizer ({(w : G)} : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) := hP.trans he.symm
  have hwT := (D.doubledOrbit_E322 h).le_sylow w.property
  have hzfix (x : G) (hx : x ∈ (T : Subgroup G)) : x * z = z * x := hzT.2 x hx
  have hTGz : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    fun x hx => mem_centralizer_singleton_iff.mpr (hzfix x hx)
  have hGz : centralizer ({z} : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
      (isTwoLocal_involution_centralizer hz) hTGz
  have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
    (fun he => hw (Subtype.ext he))
  have hB : IsPGroup 2 (zpowers (w : G)) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hw2)
  have hBH : zpowers (w : G) ≤ centralizer ({(w : G)} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hBC : centralizer (zpowers (w : G) : Set G) =
      centralizer ({(w : G)} : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hHN : centralizer ({(w : G)} : Set G) ≤ normalizer (zpowers (w : G) : Set G) :=
    hBC ▸ Subgroup.centralizer_le_normalizer _
  refine ⟨P,hP,Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer hw2),
    ⟨hGz,Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer hz),?_⟩,?_,hz,?_,?_,le_rfl⟩
  · rw [hPT]
    exact inf_le_left.trans hTGz
  · exact centralizer_pCoreIn_inf_le hB hBH (zpowers_le.mpr (hTGz hwT)) hHN hBC.le
  · rw [hPT]
    exact ⟨hzT.1,mem_centralizer_singleton_iff.mpr (hzfix w hwT).symm⟩
  · intro x hx
    rw [hPT] at hx
    exact hzfix x hx.1

/-- With the odd core discharged, failure of characteristic two supplies an
actual component with every original 1.1.5 model/action clause. -/
theorem doubleNatural_pure_component_alternative_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ z : G, orderOf z = 2 → z ∈ centerIn (T : Subgroup G) →
      generalizedFitting (centralizer ({(w : G)} : Set G)) =
        pCore 2 (centralizer ({(w : G)} : Set G)) ∨
      ∃ K : Subgroup (centralizer ({(w : G)} : Set G)),
        IsComponent (centralizer ({(w : G)} : Set G)) K ∧
        K.map (centralizer ({(w : G)} : Set G)).subtype =
          ⁅K.map (centralizer ({(w : G)} : Set G)).subtype,zpowers z⁆ ∧
        ¬ K.map (centralizer ({(w : G)} : Set G)).subtype ≤ centralizer ({z} : Set G) ∧
        HasModelAction115 K z := by
  let := D.doubledOrbit_elementary h
  intro S hns hs w hw hp hfix z hz hzT
  by_cases hc : generalizedFitting (centralizer ({(w : G)} : Set G)) =
      pCore 2 (centralizer ({(w : G)} : Set G))
  · exact Or.inl hc
  · obtain ⟨K,hK⟩ := exists_component_of_oddCore_eq_bot
      (D.doubleNatural_pure_oddCore_eq_bot_of_many h hmany B S hns w hw hp) hc
    obtain ⟨P,_,hP⟩ := D.doubleNatural_pure_component_setup_of_many h hmany B S hs w hw hp hfix z hz hzT
    exact Or.inr ⟨K,hK,Chapter1.lemma_1_1_5_three_knownSimple
      h.simpleQTKE _ P _ z hP K hK⟩

/-- In dimension five, the original conclusions hold unless an actual component
from 1.1.5 survives. The missing model exclusion remains with the assembly owner
`qt-d-double-natural-pure-fusion`; this is not the assertion of 12.1.6. -/
theorem doubleNatural_five_pure_conclusions_or_component_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ z : G, orderOf z = 2 → z ∈ centerIn (T : Subgroup G) →
      (B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes) ∨
      ∃ K : Subgroup (centralizer ({(w : G)} : Set G)),
        IsComponent (centralizer ({(w : G)} : Set G)) K ∧
        K.map (centralizer ({(w : G)} : Set G)).subtype =
          ⁅K.map (centralizer ({(w : G)} : Set G)).subtype,zpowers z⁆ ∧
        ¬ K.map (centralizer ({(w : G)} : Set G)).subtype ≤ centralizer ({z} : Set G) ∧
        HasModelAction115 K z := by
  let := D.doubledOrbit_elementary h
  intro S hns w hw hp hfix z hz hzT
  have hs : S.MarkedAmbientSylow D.sylow_normalizes_component := by
    intro v hv hpv hfixv
    exact (D.doubleNatural_five_marked_pure_sylow_of_many h hmany B hW S v hv hpv hfixv).2
  rcases D.doubleNatural_pure_component_alternative_of_many h hmany B S hns hs
    w hw hp hfix z hz hzT with hc | hK
  · exact Or.inl (D.doubleNatural_five_pure_conclusions_of_one_characteristicTwo_of_many
      h hmany B hW S hns w hw hp hc)
  · exact Or.inr hK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
