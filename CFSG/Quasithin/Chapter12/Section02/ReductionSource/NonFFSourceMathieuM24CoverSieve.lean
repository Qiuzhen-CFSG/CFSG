module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24FullQuotient
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerCoverSieve

/-!
# The central-cover branch of the marked M₂₄ centralizer

Restrict the actual quotient Sylow to the normal containing component.
The original residual still has order 17280 and elementary two-core of order
sixteen. The three-cover inspection therefore identifies every nonsimple
containing row with the concrete 3·M₂₂. No new local marking or quotient is
chosen. The simple containing rows remain explicit source obligations with
qt-d-1222-nonff-mathieu, before its full cubic quotient and ambient assembly.

Source: Aschbacher–Smith, A.3.12 and 8.2.13, printed pp.47–48 and 722–723.
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

/-- The original centralizer quotient has a normal containing component
which is either simple in the full source catalogue or the concrete 3·M₂₂.
All nonsimple source alternatives are discharged. -/
theorem sourceOrbit_m24_centralizer_quotient_simple_or_triple
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
    let B := MathieuSextet.pointResidualImage L (z : G)
    ∃ K : Subgroup (C ⧸ pCore 2 C),
      K.IsCComponent ∧ K.Normal ∧ B < K ∧ IsQuasisimple K ∧
      ((IsSimpleGroup K ∧ Chapter1.Section02.LocalModels.TheoremCModel K) ∨
        Nonempty (K ≃* M22TripleCover)) := by
  obtain ⟨K,hKC,hK,hBK,hqs,hm⟩ :=
    D.sourceOrbit_m24_centralizer_quotient_containing h hmany hV hq hnon a E hE z hz hne
  refine ⟨K,hKC,hK,hBK,hqs,?_⟩
  rcases hm with hs | ⟨hc,hm⟩
  · exact .inl hs
  · right
    let := hqs
    let B := MathieuSextet.pointResidualImage L (z : G)
    obtain ⟨hel,hcore,_,hcard⟩ :=
      D.sourceOrbit_m24_centralizer_quotient_residual_structure h hmany hV hq hnon a E hE z hz hne
    let := hel
    obtain ⟨P,_,hl,_⟩ :=
      D.sourceOrbit_m24_centralizer_quotient_local h hmany hV hq hnon a E hE z hz hne
    obtain ⟨S,_,hlocal⟩ :=
      ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction P hl hBK.le hKC.subnormal
    have hproper : B.subgroupOf K ≠ ⊤ := by
      intro ht
      exact hBK.not_ge (subgroupOf_eq_top.mp ht)
    have hbc : Nat.card (B.subgroupOf K) = 17280 :=
      (Nat.card_congr (subgroupOfEquivOfLe hBK.le).toEquiv).trans hcard
    have hr : 4 ≤ primeRank 2 K := by
      have hh := IsElementaryAbelian.log_card_eq_primeRank (p := 2) (pCore 2 B)
      rw [hcore] at hh
      have hfour : primeRank 2 (pCore 2 B) = 4 := by norm_num at hh; omega
      rw [←hfour]
      exact (Theory.GroupTheory.primeRank_le_of_injective 2 (pCore 2 B).subtype
        (pCore 2 B).subtype_injective).trans
          (Theory.GroupTheory.primeRank_le_of_injective 2 (inclusion hBK.le)
            (inclusion_injective hBK.le))
    have hzcard : Nat.card (center K) = 3 := by
      rw [Nat.card_congr hc.some.toEquiv]
      simp
    exact MathieuSextet.triple_cover_of_local_residual S (B.subgroupOf K)
      hlocal hproper hbc hr hzcard hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
