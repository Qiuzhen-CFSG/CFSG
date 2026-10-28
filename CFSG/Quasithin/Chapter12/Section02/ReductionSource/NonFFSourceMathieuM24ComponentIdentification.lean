module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24CoverSieve
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerNormalCore

/-!
# Identifying the original full centralizer quotient

The original point residual has elementary core of order sixteen, full
3·A₆ quotient, and order 17280. Restrict the original Sylow and the faithful
degree-twelve action to the normal containing component. The simple source
catalogue is excluded by the exact carrier inspections, leaving the actual
3·M₂₂ component. The existing extension theorem then identifies the FULL
centralizer quotient with the concrete 3·M₂₂·2 and supplies its surjection
to Aut(M₂₂), retaining the kernel of order three.

Source: Aschbacher–Smith 8.2.13, printed pp.722–723, using A.3.12.
Whole-orbit selection and ambient Aschbacher–Segev recognition retain their
independent producers; neither is claimed by this quotient identification.
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative

public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The normal component in the actual full centralizer quotient is 3·M₂₂. -/
theorem sourceOrbit_m24_centralizer_quotient_triple_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let C := centralizer ({(z : G)} : Set G)
    ∃ K : Subgroup (C ⧸ pCore 2 C), K.Normal ∧ Nonempty (K ≃* M22TripleCover) := by
  obtain ⟨K,hKC,hK,hBK,hqs,hm⟩ :=
    D.sourceOrbit_m24_centralizer_quotient_simple_or_triple h hmany hV hq hnon a E hE z hz hne
  refine ⟨K,hK,?_⟩
  rcases hm with ⟨_,hm⟩ | hm
  · exfalso
    let := hqs
    let B := MathieuSextet.pointResidualImage L (z : G)
    obtain ⟨hel,hcore,⟨eqB⟩,hcard⟩ :=
      D.sourceOrbit_m24_centralizer_quotient_residual_structure h hmany hV hq hnon a E hE z hz hne
    let := hel
    obtain ⟨P,_,hl,hPB⟩ :=
      D.sourceOrbit_m24_centralizer_quotient_local h hmany hV hq hnon a E hE z hz hne
    obtain ⟨S,hS,hlocal⟩ :=
      ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction P hl hBK.le hKC.subnormal
    have hSN : (S : Subgroup K) ≤ normalizer (B.subgroupOf K : Set K) := by
      rw [hS,←subgroupOf_normalizer_eq hBK.le]
      exact comap_mono hPB
    have hproper : B.subgroupOf K ≠ ⊤ := by
      intro ht
      exact hBK.not_ge (subgroupOf_eq_top.mp ht)
    let b := subgroupOfEquivOfLe hBK.le
    let bc : pCore 2 (B.subgroupOf K) ≃* pCore 2 B :=
      (b.subgroupMap (pCore 2 (B.subgroupOf K))).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
    let : IsElementaryAbelian 2 (pCore 2 (B.subgroupOf K)) :=
      IsElementaryAbelian.of_injective bc.toMonoidHom bc.injective
    have hbc : Nat.card (B.subgroupOf K) = 17280 :=
      (Nat.card_congr b.toEquiv).trans hcard
    have hcc : Nat.card (pCore 2 (B.subgroupOf K)) = 16 :=
      (Nat.card_congr bc.toEquiv).trans hcore
    have hcq : Nat.card ((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) = 1080 := by
      rw [Nat.card_congr (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).toEquiv,
        Nat.card_congr eqB.toEquiv,Atlas.Codes.hexEven_card]
    have hr : 4 ≤ primeRank 2 K := by
      have hh := IsElementaryAbelian.log_card_eq_primeRank (p := 2) (pCore 2 B)
      rw [hcore] at hh
      have hfour : primeRank 2 (pCore 2 B) = 4 := by norm_num at hh; omega
      rw [←hfour]
      exact (Theory.GroupTheory.primeRank_le_of_injective 2 (pCore 2 B).subtype
        (pCore 2 B).subtype_injective).trans
          (Theory.GroupTheory.primeRank_le_of_injective 2 (inclusion hBK.le)
            (inclusion_injective hBK.le))
    obtain ⟨he,ρ,hρ,hd,_⟩ :=
      D.sourceOrbit_m24_centralizer_quotient_faithful_action h hmany hV hq hnon a E hE z hz hne
    let := he
    exact MathieuSextet.not_simple_containing S (B.subgroupOf K) hlocal hSN hproper hbc hcc hcq hr
      (ρ.comp K.subtype) (hρ.comp K.subtype_injective) hd hm
  · exact hm

/-- The full original quotient, including the genuine cubic kernel. -/
theorem sourceOrbit_m24_centralizer_quotient_extension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let C := centralizer ({(z : G)} : Set G)
    Nonempty ((C ⧸ pCore 2 C) ≃*
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.actionGroup) ∧
      ∃ π : (C ⧸ pCore 2 C) →* MulAut M22, Function.Surjective π ∧ Nat.card π.ker = 3 := by
  exact D.sourceOrbit_m24_centralizer_quotient_extension_of_component
    h hmany hV hq hnon a E hE z hz hne
    (D.sourceOrbit_m24_centralizer_quotient_triple_component h hmany hV hq hnon a E hE z hz hne)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
