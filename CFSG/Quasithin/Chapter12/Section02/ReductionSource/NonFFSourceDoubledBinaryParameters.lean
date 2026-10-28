module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlanes
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction

/-!
# Binary doubled parameters and the single-plane reduction

The actual orbit has a=1: an elementary four-group in the second fixed-space
family would have to fix its entire element-fixed-space span, of dimension
at least five, although its common fixed space has dimension at most three.
The marked transvection gives m≤2 and the non-FF hypothesis gives m≥2.

The proved E.6.11 moving-element theorem discharges the structural premise
in the paired-plane reduction. Thus the centralizer containment for one
paired plane gives r≥3. Its local centralizer preserves the original seed.
The numerical values give s=2 and w≥1; with the still-explicit upper bound
w≤1, the existing equality-case argument supplies an actual noncommuting
conjugate pair and its rank-five reverse normalizer hyperplane.

The source 7.7.3 containment and the global w upper bound remain obligations
of qt-d-1222-nonff-doubled, as do the subsequent centralizer-core and pair
arguments. This module does not assert the completed binary exclusion.
Source: Aschbacher–Smith 7.2.1,7.3.3,7.6.1 and7.7.1–4,
printed pp.698–704, in `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The first fixed-space family is the last nonempty family on the actual orbit. -/
theorem sourceOrbit_binary_localA_eq_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : localA D.sourceOrbit = 1 := by
  let ρ := automizerRepresentation D.sourceOrbit
  have hinj := automizerRepresentation_injective D.sourceOrbit
  have hr := D.sourceOrbit_binary_automizer_rank_eq h hd F hF hmodel
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    rintro ⟨A,hA⟩
    suffices k ≤ 1 from by exact_mod_cast this
    by_contra hk
    let : IsElementaryAbelian 2 A := hA.2.1.2
    have hkr := parameter_le_rank_of_mem_fixedSpaceFamily ρ hinj hA
    have hAr := offender_rank_le_primeRank A
    rw [hr] at hAr
    have hrA : rank A = 2 := by omega
    have hcA : Nat.card A = 4 := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
      have he := hrA
      rw [rank,hn,Nat.log_pow (by decide)] at he
      rw [hn,he]
      rfl
    obtain ⟨hspan,hinner,houter⟩ := D.sourceOrbit_binary_four_dimensions h hd F hF hmodel A
      inferInstance hcA
    change 5 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) at hspan
    have hle : fixedSpaceSpan ρ A ≤ fixedSpace ρ A := by
      apply fixedSpaceSpan_le
      intro a ha hane
      have ha2 : orderOf a = 2 :=
        orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hane
      have hidx : (zpowers a).relIndex A = 2 := by
        have hp := relIndex_mul_relIndex (⊥ : Subgroup (Automizer D.sourceOrbit))
          (zpowers a) A bot_le (zpowers_le.mpr ha)
        rw [relIndex_bot_left,relIndex_bot_left,Nat.card_zpowers,ha2,hcA] at hp
        omega
      rw [← hA.2.2 (zpowers a) (zpowers_le.mpr ha) (by rw [hidx]; norm_num; omega)]
    have hdim := Submodule.finrank_mono hle
    by_cases hi : A ≤ inducedAutomizer D.sourceOrbit L
    · have hh := hinner hi
      change Module.finrank (ZMod 2) (fixedSpace ρ A) = 3 at hh
      omega
    · have hh := houter hi
      change Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2 at hh
      omega
  · have hpos : 0 < primeRank 2 (Automizer D.sourceOrbit) := by omega
    have hex : ∃ A : Subgroup (Automizer D.sourceOrbit),
        IsElementaryAbelian 2 A ∧ 1 < Nat.card A := by
      by_contra! hn
      have hz := (primeRank_le_iff_elementary_card_le (p := 2) (n := 0)
        (Automizer D.sourceOrbit)).mpr (fun A hA => by simpa using hn A hA)
      omega
    obtain ⟨A,hA,hc⟩ := hex
    have hne : A ≠ ⊥ := by rintro rfl; simp at hc
    exact le_moduleA_of_mem ρ ((mem_fixedSpaceFamily_one_iff ρ A).mpr ⟨hne,hA⟩)


/-- The table's involution parameter on the literal binary doubled orbit. -/
theorem sourceOrbit_binary_localM_eq_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) : localM D.sourceOrbit = 2 := by
  apply le_antisymm
  · obtain ⟨_,_,_,q,hq,E,f,hE,hf,_⟩ := D.sourceOrbit_binary_automizer_model h hd F hF hmodel
    exact doubledBinary_moduleM_le_two (automizerRepresentation D.sourceOrbit)
      (D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
        (inclusion D.sourceOrbit_component_normalizes)) q hq E hE f hf
  · have hn := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
    apply le_csInf ⟨_,Set.mem_insert _ _⟩
    rintro n (rfl | ⟨a,ha,rfl⟩)
    · rw [D.sourceOrbit_binary_dimension h hd F hF hmodel]
      decide
    · obtain ⟨hA,hr,_,_⟩ := involution_actor_rank_and_fixedCodim
        (automizerRepresentation D.sourceOrbit) a ha
      by_contra hh
      exact hn ⟨zpowers a,hA,by omega⟩

open DoubledBinaryPlanes
/-- The exact E.6.11 action input is now discharged. The only local
centralizer premise is the one paired plane in source 7.7.3. -/
theorem sourceOrbit_binary_singlePlane_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* Group, Function.Surjective q ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ l w, E (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l w) = NaturalDual.action (q l) (E w)) ∧
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          (normalizer (L : Set G) ⊓ centralizer (ambientPlane D.sourceOrbit E v f : Set G) ≤
            normalizer (V : Set G)) ∧
          (centralizer (ambientPlane D.sourceOrbit E v f : Set G) ≤ normalizer (L : Set G) →
            3 ≤ globalR D.sourceOrbit) := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,_,hinner,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  have hN := D.sourceOrbit_normalizer_eq_of_markedDoubled h hd
  have hmark : ∀ l w, E (automizerRepresentation D.sourceOrbit
      (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
        (inclusion D.sourceOrbit_component_normalizes l)) w) = NaturalDual.action (q l) (E w) := hE
  refine ⟨t,ht,hnt,q,hq,E,hE,hV,hVt,?_⟩
  intro v f hfv
  constructor
  · rintro x ⟨hx,hxc⟩
    let n : normalizer (D.sourceOrbit : Set G) := ⟨x,hN.symm ▸ hx⟩
    exact (hinner n).mp (doubledBinary_ambientPlane_fixer_inner
      D.sourceOrbit E a hcov n v f hfv hxc)
  · intro hC
    have hp := all_plane_centralizers D.sourceOrbit L D.sourceOrbit_component_normalizes E q
      hmark hq v f hfv (hN.symm ▸ hC)
    have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
    rw [← hN] at h61
    exact three_le_globalR_of_planes D.sourceOrbit E a hcov h61
      (fun _ hU hmax hn => Section06.maximal_escape_action_knownSimple h61 hU hmax hn) hp

/-- The proved table values and lower r bound give s=2 and w≥1 on the
original orbit, the lower half of the parameter equality used in 7.6.1. -/
theorem sourceOrbit_binary_small_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hr : 2 ≤ globalR D.sourceOrbit) :
    localM D.sourceOrbit = 2 ∧ localA D.sourceOrbit = 1 ∧
      globalS D.sourceOrbit = 2 ∧ 1 ≤ globalW D.sourceOrbit T := by
  have hm := D.sourceOrbit_binary_localM_eq_two h hd F hF hmodel hnon
  have ha := D.sourceOrbit_binary_localA_eq_one h hd F hF hmodel
  have hs : globalS D.sourceOrbit = 2 := by
    rw [globalS,hm]
    exact min_eq_right hr
  refine ⟨hm,ha,hs,?_⟩
  have hw := Chapter7.globalS_le_globalW_add_localA D.sourceOrbit_weakClosure_setup
  rw [hs,ha] at hw
  by_contra hh
  have hz : globalW D.sourceOrbit T = 0 := by
    exact Order.lt_one_iff.mp (lt_of_not_ge hh)
  rw [hz] at hw
  norm_num at hw

/-- Application to the original noncommuting conjugate pair. Only the
source upper bound w≤1 and the single-plane centralizer containment remain;
the E.6.11 action input and all displayed parameter values are proved. -/
theorem sourceOrbit_binary_singlePlane_offender
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          centralizer (ambientPlane D.sourceOrbit E v f : Set G) ≤ normalizer (L : Set G) →
          localM D.sourceOrbit = 2 ∧ localA D.sourceOrbit = 1 ∧ globalS D.sourceOrbit = 2 ∧
          globalW D.sourceOrbit T = 1 ∧ globalR D.sourceOrbit = 3 ∧
          ∃ g : G,
            ⁅D.sourceOrbit,D.sourceOrbit.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
            inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g) ≤
              inducedAutomizer D.sourceOrbit L ∧
            Nat.card (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) :
              Subgroup G) = 8 ∧
            offenderFixedSpan D.sourceOrbit g = D.sourceOrbit ⊓
              normalizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) ∧
            (offenderFixedSpan D.sourceOrbit g).relIndex D.sourceOrbit = 2 ∧
            rank (offenderFixedSpan D.sourceOrbit g) = 5 := by
  obtain ⟨t,ht,hnt,_,_,E,_,hV,hVt,hp⟩ :=
    D.sourceOrbit_binary_singlePlane_reduction h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv hC
  have hr := (hp v f hfv).2 hC
  obtain ⟨hm,ha,hs,_⟩ := D.sourceOrbit_binary_small_parameters h hd F hF hmodel hnon
    (le_trans (by decide : (2 : ℕ∞) ≤ 3) hr)
  obtain ⟨hwe,hre,_,_⟩ := D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr
  exact ⟨hm,ha,hs,hwe,hre,
    D.sourceOrbit_binary_exists_offender_geometry h hd F hF hmodel hnon hw hr⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
