module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.MultiplicitySimple
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.PointLines

/-!
# Original Mathieu application of the faithful four-space and its three copies

The same marked M₂₄ data and full cubic quotient construct the source
three-space. Its literal N_G(Z)/R and S/R actions on R/Z are faithful.
The original pair section has rank four and carries a faithful irreducible
S/R action, also irreducible on the marked A₅. Three copies, with precisely
this action, give R/Z. Point-core intersections respect the Fano-line law
on the same Z.

No representation or geometry premise is added. The remaining natural
module identifications, full tensor action and ambient recognition are
not conclusions of these exports.

Source: Aschbacher–Smith 8.2.12–14, printed pp.722–723;
Aschbacher–Segev (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Faithfulness and the exact original radical centralizer, with no new source inputs. -/
theorem sourceOrbit_m24_three_space_faithful_radical
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
        pCore 2 (centralizer ({(z : G)} : Set G))))) :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X),
      letI := d.R_normal_in_S_intrinsic
      letI := d.R_normal_in_normalizer
      Function.Injective (d.SRadicalAction ht) ∧
      Function.Injective (d.radicalQuotientAction ht) ∧
      d.radicalAction.ker = d.R.subgroupOf (normalizer (d.space : Set G)) ∧
      normalizer (d.space : Set G) ⊓ centralizer (d.R : Set G) = d.space := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  exact ⟨cubic,X,d,d.SRadicalAction_injective ht,d.radicalQuotientAction_injective ht,
    d.radicalAction_ker ht,d.normalizer_radical_centralizer ht⟩

/-- The actual faithful four-space, three-copy action and Fano-line relation. -/
theorem sourceOrbit_m24_three_space_multiplicity
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
        pCore 2 (centralizer ({(z : G)} : Set G))))) :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X),
      letI := d.R_normal_in_S_intrinsic
      letI := d.R_normal_in_normalizer
      Nat.card d.multiplicitySpace = 16 ∧
      primeRank 2 d.multiplicitySpace = 4 ∧
      Function.Injective (d.multiplicityAction ht) ∧
      (∀ U : Subgroup d.multiplicitySpace,
        (∀ a : alternatingGroup (Fin 5), ∀ w : d.multiplicitySpace,
          w ∈ U → d.markedMultiplicityAction ht a w ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      (∀ s : d.S, ∀ w : d.multiplicitySpace,
        (d.markedMultiplicityAction ht (d.SQuotientEquiv ht (QuotientGroup.mk' _ s)) w :
            d.R ⧸ center d.R) =
          d.radicalAction (inclusion (Subgroup.centralizer_le_normalizer _) s) w) ∧
      (∀ t ∈ d.space, ∀ u ∈ d.space, t ≠ 1 → u ≠ 1 → t ≠ u →
        d.coreSection t ⊓ d.coreSection (t*u) = d.coreSection t ⊓ d.coreSection u) ∧
      ∃ f : d.multiplicitySpace × (d.multiplicitySpace × d.multiplicitySpace) ≃*
          (d.R ⧸ center d.R),
        (∀ w, f (w,1,1) = (w : d.R ⧸ center d.R)) ∧
        ∀ a : d.S ⧸ d.R.subgroupOf d.S, ∀ u v w : d.multiplicitySpace,
          f (d.multiplicityAction ht a u,d.multiplicityAction ht a v,d.multiplicityAction ht a w) =
            d.SRadicalAction ht a (f (u,v,w)) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  refine ⟨cubic,X,d,d.multiplicitySpace_card ht,d.multiplicitySpace_rank ht,
    d.multiplicityAction_injective ht,d.multiplicity_alternating_irreducible ht,
    d.markedMultiplicityAction_mk ht,?_,d.exists_multiplicity_coordinates ht⟩
  intro t htZ u huZ ht1 hu1 htu
  exact d.coreSection_inf_product ht htZ huZ ht1 hu1 htu

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
end
