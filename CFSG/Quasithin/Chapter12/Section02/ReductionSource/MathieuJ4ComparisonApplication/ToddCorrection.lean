module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCore

/-!
# The original Mathieu branch's full-word correction

The unchanged marked-M24 hypotheses produce the same IsTypeJ4 witness.
Its earlier LocalData gives the actual overlap, cubic and point radical.
The first application recovers Q from O2(I) and that cubic, then constructs
an outer correction of I which descends through the full Q A. The second
chooses the same Todd outer class to fix any specified odd-order subgroup
and preserve its normalizer in the literal S intersect M, with both flags.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
These applications do not assert the full overlap automorphism theorem,
edge reversal, or unconditional J4 recognition.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour SourceComparison SourceRecognition
open LocalGeometry.LocalSubgroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same original cubic recovers Q and supports the constructed
correction descending through the literal Q A quotient. -/
theorem sourceOrbit_m24_cubic_todd_correction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    ⁅pCore 2 (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))),
      (cubicSylowImage data.e data.X).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G)))⁆ =
      (core (z : G)).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))) ∧
    (¬ ∃ x : data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G)),
      planeOverlapToddTwist data (cubicFixedWord data) = MulAut.conj x) ∧
    (∀ y : pointCubic data, pointTwist data (cubicFixedWord data) y.val = y.val) ∧
    ((core (z : G)).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G)))).map
        (planeOverlapToddTwist data (cubicFixedWord data)).toMonoidHom =
      (core (z : G)).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))) ∧
    ((twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G)))).map
        (planeOverlapToddTwist data (cubicFixedWord data)).toMonoidHom =
      (twoThreeCore (Recognition.JankoFour.centralizer (z : G))).subgroupOf
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))) ∧
    cubicToddQuotientTwist data ^ 2 = 1 ∧
    (∀ x : data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G)),
      cubicToddQuotientTwist data (QuotientGroup.mk' _ x) =
        QuotientGroup.mk' _ (planeOverlapToddTwist data (cubicFixedWord data) x)) := by
  exact ⟨overlap_core_eq_commutator data,cubic_todd_correction data⟩

/-- The original relative normalizer used by the Section 8 edge argument
is preserved by a constructed representative of the Todd outer class. -/
theorem sourceOrbit_m24_odd_normalizer_correction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (Y : Subgroup data.P.M) (hY : Odd (Nat.card Y)) :
    ∃ (w : Full) (v : Cocode), w ∉ Core ∧
      pointTwist data w =
        MulAut.conj (data.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd v))) *
          pointTwist data toddOddWord ∧
      pointTwist data w ^ 2 = 1 ∧
      (∀ y : Y, pointTwist data w y.val = y.val) ∧
      (¬ ∃ x : pointOverlap data, overlapToddTwist data w = MulAut.conj x) ∧
      ((Recognition.JankoFour.centralizer (z : G)).subgroupOf data.P.M).map
          (pointTwist data w).toMonoidHom =
        (Recognition.JankoFour.centralizer (z : G)).subgroupOf data.P.M ∧
      (data.L.G₂.subgroupOf data.P.M).map (pointTwist data w).toMonoidHom =
        data.L.G₂.subgroupOf data.P.M ∧
      ((data.d.S.subgroupOf data.P.M) ⊓ normalizer (Y : Set data.P.M)).map
          (pointTwist data w).toMonoidHom =
        (data.d.S.subgroupOf data.P.M) ⊓ normalizer (Y : Set data.P.M) :=
  exists_odd_point_correction data Y hY

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
