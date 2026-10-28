module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.JankoResidual
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
public import Theory.GroupTheory.PResidual.OddConjugateSpan
/-!
# The original odd actor's closure and the Mathieu residual comparison

Put X = ⟨A^T⟩ for the literal odd section actor. The subgroup X is
two-perfect; its action on L differs from the identity only by O₂(L),
which lies in T and normalizes X. Removing this normalizing two-group
error proves that LT normalizes X. The Sylow overgroup XT lies in the
characteristic-two group N_G(L), so X inherits characteristic two.
Its nontrivial two-core and the established uniqueness of LT then give
N_G(X) ≤ N_G(L), without assuming uniqueness of L_A.

Every T-normalized comparison group on whose two-core quotient A acts
trivially normalizes the same X and hence lies in N_G(L). The application
uses the full J₄ component and its literal involution-centralizer residual.
The Hall consumer retains both original J₄ configurations and constructs
this normalizer control without a callback. The order-three pushing-up
argument, fixed-line identification, odd-local comparison group and equality
K = ⟨L_A,K_Z⟩ still require proofs; this module does not assert Hall faithfulness.

Source: Aschbacher--Smith, 4.4.3, final paragraph on printed p.623,
and the application to 4.4.14, printed pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The literal T-closure of an odd section actor is normalized by L. -/
theorem odd_actor_closure_normalized (T : Sylow 2 G) (L A : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hA : A ≤ sectionCentralizer L) (ho : Odd (Nat.card A)) :
    L ⊔ (T : Subgroup G) ≤ normalizer (conjugateSpanBy A (T : Subgroup G) : Set G) := by
  let X := conjugateSpanBy A (T : Subgroup G)
  have hC : sectionCentralizerIn (normalizer (L : Set G)) L = sectionCentralizer L :=
    inf_eq_right.mpr ((le_sectionCentralizer_iff _ _).mp le_rfl).1
  have hnC : (T : Subgroup G) ≤ normalizer (sectionCentralizer L : Set G) := by
    rw [←hC]
    exact hTL.trans (sectionCentralizerIn_normalized le_rfl)
  have hXC : X ≤ sectionCentralizer L := conjugateSpanBy_le hA hnC
  have hc : ⁅L,X⁆ ≤ L.pCoreIn 2 := by
    rw [commutator_comm]
    exact ((le_sectionCentralizer_iff _ _).mp hXC).2
  have hcore : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_mono_of_normalizes (p := 2)
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer hTL)
    have ht := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype at ht
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] at ht
    exact hh.trans ht
  exact sup_le (le_normalizer_of_isPPerfect_of_commutator_le X L (L.pCoreIn 2)
    (isPPerfect_conjugateSpanBy_of_coprime A _ ho.coprime_two_left)
    (isPGroup_pCoreIn 2 L)
    (hcore.trans (le_normalizer_conjugateSpanBy A (T : Subgroup G))) hc)
    (le_normalizer_conjugateSpanBy A (T : Subgroup G))
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The odd actor's original T-closure has nontrivial two-core and its full
normalizer lies in N_G(L). No residual uniqueness input is needed. -/
theorem sourceOrbit_oddActorClosure_control
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hne : A ≠ ⊥) (hA : A ≤ sectionCentralizer L)
    (ho : Odd (Nat.card A)) :
    let X := conjugateSpanBy A (T : Subgroup G)
    IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
      normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  let M := normalizer (L : Set G)
  let X := conjugateSpanBy A (T : Subgroup G)
  let Y := X ⊔ (T : Subgroup G)
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hXM : X ≤ M := conjugateSpanBy_le ((le_sectionCentralizer_iff _ _).mp hA).1
    (hTM.trans M.le_normalizer)
  have hYM : Y ≤ M := sup_le hXM hTM
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right
  have hYX : Y ≤ normalizer (X : Set G) :=
    sup_le X.le_normalizer (le_normalizer_conjugateSpanBy A (T : Subgroup G))
  have hXne : X ≠ ⊥ := fun hh => hne
    (bot_unique (hh ▸ le_conjugateSpanBy A (T : Subgroup G)))
  have hu := h.sylow_normalized_maximal_unique hTM
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hcM := h.simpleQTKE.evenCharacteristic T M hu.1 hTM
  have hcY : Y ⊓ centralizer (Y.pCoreIn 2 : Set G) ≤ Y.pCoreIn 2 := by
    have hc := centralizer_pCore_le_of_sylow_le (T.subtype hTM) (Y.subgroupOf M)
      (fun x hx => hTY hx) hcM
    exact Chapter1.mem_He_iff.mpr
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hYM)).mp hc)
  have hcX : X ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ X.pCoreIn 2 :=
    pCoreIn_selfCentralizing_of_subnormal hcY (show X ≤ Y from le_sup_left)
      (normal_subgroupOf_of_le_normalizer hYX).isSubnormal
  have hcore : X.pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hbot : centralizer (X.pCoreIn 2 : Set G) = ⊤ := by
      rw [hh]
      ext x
      simp [mem_centralizer_iff]
    rw [hbot, hh, inf_top_eq] at hcX
    exact hXne (bot_unique hcX)
  have hnorm := odd_actor_closure_normalized T L A hTM hA ho
  refine ⟨isPPerfect_conjugateSpanBy_of_coprime A _ ho.coprime_two_left,
    hcore,hnorm,?_⟩
  exact (normalizer_le_normalizer_characteristic_image X (pCore 2 X)).trans
    (normalizer_le_of_unique_maximalTwoLocal hu.2 (isPGroup_pCoreIn 2 X) hcore
      (hnorm.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))

/-- The comparison group in the last paragraph of 4.4.3 is contained in M
once the literal actor centralizes its two-core quotient. -/
theorem sourceOrbit_oddActor_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hne : A ≠ ⊥) (hA : A ≤ sectionCentralizer L)
    (ho : Odd (Nat.card A))
    (Q : Subgroup G) (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hAQ : A ≤ sectionCentralizer Q) : Q ≤ normalizer (L : Set G) :=
  (le_sup_left.trans (odd_actor_closure_normalized T Q A hTQ hAQ ho)).trans
    (D.sourceOrbit_oddActorClosure_control h A hne hA ho).2.2.2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The terminal comparison permits the source's replacement I_Z inside
L_Z. Only T-normalization is required of this replacement; ambient normality
is not imposed. The original residual and covering component are unchanged. -/
theorem sourceOrbit_janko_residual_comparison_of_overgroup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hne : A ≠ ⊥) (hA : A ≤ sectionCentralizer L)
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (z : K) (I : Subgroup G)
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (hAI : A ≤ sectionCentralizer I)
    (hRI : ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)
    (hgen : K.map (normalizer (A : Set G)).subtype = oddActorResidual L A ⊔
      ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype)) : False := by
  apply hout
  rw [hgen]
  exact sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
    (hRI.trans (D.sourceOrbit_oddActor_comparison h A hne hA ho I hTI hAI))

/-- Apply the odd-actor comparison to the literal centralizer residual and
its actual ambient normal component. The two displayed premises are the
remaining source generation and odd-local identification steps. -/
theorem sourceOrbit_janko_residual_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hne : A ≠ ⊥) (hA : A ≤ sectionCentralizer L)
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (z : K)
    (hTz : (T : Subgroup G) ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G))
    (hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G))
    (Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)))
    [Q.Normal]
    (hRQ : ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype) ≤
      Q.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype)
    (hgen : K.map (normalizer (A : Set G)).subtype = oddActorResidual L A ⊔
      ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype))
    (hcomm : ⁅A,Q.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype⁆ ≤
      (Q.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype).pCoreIn 2) :
    False := by
  let C := centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)
  let Qg := Q.map C.subtype
  have hCQ : C ≤ normalizer (Qg : Set G) := by
    have hh := Q.le_normalizer_map C.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  exact D.sourceOrbit_janko_residual_comparison_of_overgroup h A hne hA ho K hout z
    Qg (hTz.trans hCQ) ((le_sectionCentralizer_iff _ _).mpr ⟨hAz.trans hCQ,hcomm⟩)
    hRQ hgen

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction retains both full J4 configurations and
now controls the full normalizer of the odd actor's T-closure. The final
comparison applies to every T-normalized group on whose two-core quotient
this same actor is trivial. This is a reduction, not Hall faithfulness. -/
theorem sourceOrbit_mathieu_hall_comparison_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpJankoInnerCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoFixedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hcase⟩ :=
    @sourceOrbit_mathieu_hall_fixed_residual G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := he
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,
    D.sourceOrbit_oddActorClosure_control h.toHypothesis1221 A hne hAC hodd,
    D.sourceOrbit_oddActor_comparison h.toHypothesis1221 A hne hAC hodd,hcase⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
