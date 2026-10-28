module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.NativeNonFF
public import Theory.SpecificGroups.Janko4.Model.SmallMathieuThompson

/-!
# Hall faithfulness for the original M₁₂ orbit

The original non-FF action makes the native elementary radical the Thompson
subgroup of a full J₄ Sylow. Its native normalizer contains a prime-23 actor,
contradicting the faithful action on the original module of order 1024.
Applying this contradiction to the actual pushing-up witness excludes the
entire M₁₂ Hall-kernel branch. No normalizer or representation premise is added
to the original Hall application.

Source: Aschbacher–Smith 4.2.13 and 4.4.14, printed pp.611–612,624–625.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original M12 pushing-up witness is impossible: non-FF promotes the
native Sylow, and its known max1 normalizer contradicts the original module size. -/
theorem sourceOrbit_pushingUp_m12_false
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) : False := by
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hdim := ((D.sourceOrbit_pushingUp_small_module h hmany hV hnon hw K hK e).1 hm).finrank
  have hVcard : Nat.card V = 1024 := by
    have hc : Nat.card D.orbitSpace = Nat.card V :=
      (Nat.card_congr D.sourceOrbitCoordinates.toEquiv).trans
        (congrArg (fun X : Subgroup G => Nat.card X) hV.symm)
    rw [←hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    decide
  obtain ⟨P,hPC,hth⟩ := D.sourceOrbit_pushingUp_m12_native_sylow
    h.toHypothesis1221 hV hfix hm hnon hw K hK e
  have hn := D.sourceOrbit_pushingUp_m12_native_radical_normalizer h.toHypothesis1221 hV hfix hm hw K hK e
  have hcent := D.sourceOrbit_pushingUp_m12_module_centralizer h.toHypothesis1221 hV hfix hm hw K hK e
  have hcore := D.sourceOrbit_pushingUp_native_normalizer_core h.toHypothesis1221 hV hfix (.inl hm) hw K hK e
  have hnat := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  have hsmall := D.sourceOrbit_pushingUp_m12_radical_elementary h.toHypothesis1221 hV hfix hm hw K hK e
  apply Janko4.not_small_module_of_thompson_radical P _ _ hth hsmall.2.1 hnat.2.1.isPGroup
    (hnat.2.2.2.2.2.2.2.1.trans hVcard)
  · exact hn.2.1.le.trans hcore.2.2.2
  · exact (congrArg (fun X : Subgroup Janko4.Model => X ⊓ centralizer
      (((V.comap (H.subtype.comp K.subtype)).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))) : Set Janko4.Model)) hn.2.1).trans hcent

open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open scoped Pointwise
universe u
/-- For the original M12 orbit, every literal odd Hall subgroup acts faithfully
on L/O2(L). All pushing-up and separate odd-normalizer witnesses are discharged. -/
theorem sourceOrbit_m12_hall_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H₀)
    (B₀ : Subgroup H₀) (hBN : B₀ ≤ (normalizer (L : Set G)).subgroupOf H₀)
    (hHall : IsHallSubgroup oddPrimes
      (B₀.subgroupOf ((normalizer (L : Set G)).subgroupOf H₀))) :
    B₀.map H₀.subtype ⊓ sectionCentralizer L = ⊥ := by
  by_contra hker
  have hsource := D.sourceOrbit_mathieu_hall_pushingUp_only
    h hmany hV (.inl hm) hnon hH hlarge B₀ hBN hHall hker
  obtain ⟨p,A,hA⟩ := hsource
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,hgap⟩ := hA
  obtain ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,hrest⟩ := hgap
  exact D.sourceOrbit_pushingUp_m12_false h hmany hV hm hnon hw K hK e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
