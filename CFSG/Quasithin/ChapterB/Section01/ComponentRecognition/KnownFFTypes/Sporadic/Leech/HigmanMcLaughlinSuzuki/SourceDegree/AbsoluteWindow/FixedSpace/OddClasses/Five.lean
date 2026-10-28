module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses.Five.Certificates
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Five

/-!
# The remaining odd five-divisibility branch of HS has three classes

The checked fixed-point argument excludes factors seven and eleven from an
element order divisible by five. For odd orders prime to three, the exact
carrier order then gives order dividing 125. Sylow conjugacy places the element
in the marked subgroup, whose 124 nonidentity normal forms have a checked
three-class cover. Thus larger mixed orders are included in the reduction,
and no element-order or centralizer catalogue is assumed.

The result supplies the five-divisibility premise of
`oddClassBound_of_small_prime_covers` in the nine-odd-class assembly.
Source: the HS class list, ATLAS HSG1-p100B0,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/; the application is
Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace
open _root_.Sporadic.LeechRelated.HS

/-- Three actual order-five classes cover the whole odd-order branch divisible
by five and prime to three, on the literal degree-100 HS carrier. -/
theorem oddFiveClassCover : OddFiveClassCover := by
  intro _hs
  change ∃ r : Fin 3 → Carrier, ∀ g : Carrier,
    Odd (orderOf g) → ¬ 3 ∣ orderOf g → 5 ∣ orderOf g → ∃ i, IsConj g (r i)
  refine ⟨OddClassBound.Five.representative, ?_⟩
  intro g ho h3 h5
  obtain ⟨t, c, hc⟩ := FiveFusion.exists_normalForm_conjugate g
    (FiveFusion.order_dvd_of_odd_five g ho h3 h5)
  have ht : t ≠ 0 := by
    intro ht
    have hg1 : (g : Carrier) = 1 := by simpa [ht, FiveFusion.normalForm] using hc
    have hd : 5 ∣ orderOf (g : Carrier) := h5
    rw [hg1, orderOf_one] at hd
    norm_num at hd
  obtain ⟨i, hi⟩ := OddClassBound.Five.normalForm_conjugate t ht
  exact ⟨i, (isConj_iff.mpr ⟨c, hc.symm⟩).symm.trans hi⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace
