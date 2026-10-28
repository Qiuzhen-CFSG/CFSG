module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.CoreSections

/-!
# Original Mathieu application of the radical quotient actions and sections

The same marked M₂₄ data and full cubic quotient construct the source
three-space. The first export retains the literal normalizer quotient,
its K/R and S/R markings, the resulting conjugation action and faithfulness
on K/R. The second constructs the original rank-eight point sections,
rank-four intersections, quadratic point-core actions and the multiplication
coordinates from the three original pair sections.

No extra splitting, local-geometry or representation premise is introduced.
The natural tensor identification and ambient J₄ recognition remain open.
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

/-- The actual quotient action, with the original marked factor maps. -/
theorem sourceOrbit_m24_three_space_quotient_action
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
      letI := d.R_normal_in_K
      letI := d.R_normal_in_S_intrinsic
      letI := d.R_normal_in_normalizer
      Function.Bijective (d.quotientProduct ht) ∧
      Function.Injective (d.KRadicalAction ht) ∧
      (∀ k : d.K, ∀ s : d.S,
        d.markedNormalizerQuotientEquiv ht
          (d.quotientProduct ht (QuotientGroup.mk' _ k,QuotientGroup.mk' _ s)) =
          (d.KAction k,d.SQuotientEquiv ht (QuotientGroup.mk' _ s))) ∧
      (∀ k : d.K, ∀ s : d.S,
        d.markedRadicalAction ht (d.KAction k,d.SQuotientEquiv ht (QuotientGroup.mk' _ s)) =
          d.radicalAction (⟨(k : G)*(s : G),
            (normalizer (d.space : Set G)).mul_mem (d.K_le_normalizer k.property)
              ((Subgroup.centralizer_le_normalizer _) s.property)⟩ : normalizer (d.space : Set G))) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  refine ⟨cubic,X,d,d.quotientProduct_bijective ht,d.KRadicalAction_injective ht,?_,
    d.markedRadicalAction_product ht⟩
  intro k s
  rw [d.quotientProduct_mk]
  exact d.markedNormalizerQuotientEquiv_product ht k s

/-- The original core sections and their quadratic conjugation actions, without new inputs. -/
theorem sourceOrbit_m24_three_space_core_sections
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
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X),
      (∀ t, ∀ htZ : t ∈ d.space, ∀ ht1 : t ≠ 1, Nat.card (d.coreSection t) = 256 ∧
        primeRank 2 (d.coreSection t) = 8 ∧
        ∀ a b : Recognition.JankoFour.ambientCore t, ∀ v : d.R ⧸ center d.R,
          d.radicalAction (inclusion (d.cores_normalize t htZ ht1) a)
            (d.radicalAction (inclusion (d.cores_normalize t htZ ht1) b) v * v⁻¹) =
            d.radicalAction (inclusion (d.cores_normalize t htZ ht1) b) v * v⁻¹) ∧
      (∀ t ∈ d.space, ∀ u ∈ d.space, t ≠ 1 → u ≠ 1 → t ≠ u →
        Nat.card (d.coreSection t ⊓ d.coreSection u : Subgroup (d.R ⧸ center d.R)) = 16 ∧
        d.coreSection t ⊔ d.coreSection u = ⊤) ∧
      (∀ n : normalizer (d.space : Set G), ∀ t : G,
        (d.coreSection t).map (d.radicalAction n).toMonoidHom =
          d.coreSection ((n : G)*t*(n : G)⁻¹)) ∧
      ∃ f : (d.coreSection (z : G) ⊓ d.coreSection d.r : Subgroup (d.R ⧸ center d.R)) ×
        ((d.coreSection (z : G) ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) ×
          (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R))) ≃*
            (d.R ⧸ center d.R),
        ∀ a b c, f (a,b,c) = (a : d.R ⧸ center d.R)*((b : d.R ⧸ center d.R)*(c : d.R ⧸ center d.R)) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  refine ⟨cubic,X,d,?_,?_,d.coreSection_conjugate,d.exists_coreSection_product ht⟩
  · intro t htZ ht1
    exact ⟨d.coreSection_card ht htZ ht1,d.coreSection_rank ht htZ ht1,
      d.pointCore_quadratic_action ht htZ ht1⟩
  · intro t htZ u huZ ht1 hu1 htu
    exact ⟨d.coreSection_inf_card ht htZ huZ ht1 hu1 htu,
      d.coreSection_sup ht htZ huZ ht1 hu1 htu⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
end
