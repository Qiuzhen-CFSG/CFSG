module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourNormalExclusion
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianRadicalControl

/-!
# Original radical and involution control in the Hermitian ordinary branch

The original tensor marking gives |V| = 512, and the non-FF setup kills
its fixed space. These discharge the radical-control theorem on each
actual ordinary component of the pushing-up witness. Thus O₂(J) centralizes
V, and the normalizer of its component intersection preserves V, with the
full central cover retained.

Choose an involution in the original C_V(T), lift it to that same component,
and retain the entire component-centralizer residual. Both T and O₂(J)
centralize this involution, while its residual escapes N_G(L) by the native
nine-space obstruction. The final chosen-module application constructs all
these witnesses for the original escaping noncubic actor. It does not claim
that this residual lies in N_G(L): that remaining comparison, ordinary-branch
exclusion, and the subsequent 8.2.7--13 assembly remain open.
Source: Aschbacher--Smith 4.2.13 and 4.4.3, printed pp.611--612,623,
as used in 8.2.7, p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The tensor marking discharges the native order and fixed-space premises
on the unchanged pushing-up witness and full component. -/
theorem sourceOrbit_hermitian_ordinary_radical_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    J.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) ∧
      (normalizer ((J.pCoreIn 2).comap (H.subtype.comp K.subtype) : Set K)).map
        (H.subtype.comp K.subtype) ≤ normalizer (D.sourceOrbit : Set G) := by
  obtain ⟨e⟩ := D.sourceOrbit_hermitian_field_four_ordinary_janko
    h hmany hV hnon d B eQ hfield hw K hK
  have hw' : Witness L V A J H W := by simpa only [hV] using hw
  have hfix : V ⊓ centralizer (L : Set G) = ⊥ :=
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hcard : Nat.card V = 512 := by
    rw [hV]
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    change Nat.card D.sourceOrbit = _ at hc
    rw [Nat.card_zmod,(D.hermitianOrbitCoordinates 1 d).finrank_eq,finrank_binary] at hc
    exact hc
  simpa only [hV] using D.sourceOrbit_hermitian_ordinary_radical_control_of_card
    h.toHypothesis1221 hfix hcard eQ (by rw [B.card_eq,hfield]; decide) hw' K hK e

/-- The original Sylow and radical centralize the same module involution;
its full component-centralizer residual escapes the original normalizer. -/
theorem sourceOrbit_hermitian_ordinary_radical_fixed_residual_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    ∃ z : K, ((z : H) : G) ∈ D.sourceOrbit ∧ orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({((z : H) : G)} : Set G) ∧
      J.pCoreIn 2 ≤ centralizer ({((z : H) : G)} : Set G) ∧
      ¬ ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype) ≤
          normalizer (L : Set G) := by
  have hcent := (D.sourceOrbit_hermitian_ordinary_radical_control
    h hmany hV hnon d B eQ hfield hw K hK).1
  let := D.elementary
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    hV.symm ▸ D.sourceOrbit_weakClosure_setup.normalizes
  have hf := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) V T.isPGroup'
    (IsElementaryAbelian.isPGroup 2 V) hTV D.ne_bot
  obtain ⟨v,hv,hvne⟩ :=
    (V ⊓ centralizer ((T : Subgroup G) : Set G)).bot_or_exists_ne_one.resolve_left hf
  have hc := hw.2.2.2.2.2.2.1
  have hVK : D.sourceOrbit ≤ K.map H.subtype := by
    intro v hv
    have hF := hw.2.2.2.2.2.2.2.2.2.2.1 hv
    exact ⟨⟨v,hc.component_le.trans hc.local_le hF⟩,
      hc.ordinary_component_contains_original K hK hF,rfl⟩
  obtain ⟨k,hk,hkv⟩ := hVK (hV ▸ hv.1)
  let z : K := ⟨k,hk⟩
  have hzv : ((z : H) : G) = v := hkv
  have hz : orderOf z = 2 := by
    rw [←orderOf_coe z,←orderOf_coe (z : H),hzv]
    exact orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian v hv.1,hvne⟩
  have hzV : ((z : H) : G) ∈ D.sourceOrbit := hzv.symm ▸ (hV ▸ hv.1)
  refine ⟨z,hzV,hz,?_,?_,D.sourceOrbit_hermitian_ordinary_janko_residual_escape
    h hmany hV hnon d B eQ hfield hw K hK z hzV hz⟩
  · intro t ht
    rw [hzv]
    exact mem_centralizer_singleton_iff.mpr (hv.2 t ht)
  · intro r hr
    exact mem_centralizer_singleton_iff.mpr ((hcent hr) _ hzV).symm

/-- Every actual escaping noncubic actor supplies the original ordinary
witness with radical control and a single marked involution/residual. -/
theorem sourceOrbit_hermitian_field_four_oddActor_radical_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J H W : Subgroup G, Witness L D.sourceOrbit A J H W ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
        W.subgroupOf H ≤ K ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        J.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) ∧
        (normalizer ((J.pCoreIn 2).comap (H.subtype.comp K.subtype) : Set K)).map
          (H.subtype.comp K.subtype) ≤ normalizer (D.sourceOrbit : Set G) ∧
        ∃ z : K, ((z : H) : G) ∈ D.sourceOrbit ∧ orderOf z = 2 ∧
          (T : Subgroup G) ≤ centralizer ({((z : H) : G)} : Set G) ∧
          J.pCoreIn 2 ≤ centralizer ({((z : H) : G)} : Set G) ∧
          ¬ ((solvableResidual (centralizer ({z} : Set K))).map
            (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype) ≤
              normalizer (L : Set G) := by
  obtain ⟨J,H,W,hw,K,hK,hn,houtK,hFK,hWK,he⟩ :=
    D.sourceOrbit_hermitian_field_four_oddActor_pushingUp
      h hmany hV hnon d B eQ hfield hp hgt A hne hAe hA hout
  have hr := D.sourceOrbit_hermitian_ordinary_radical_control
    h hmany hV hnon d B eQ hfield hw K hK
  exact ⟨J,H,W,hw,K,hK,hn,houtK,hFK,hWK,he,hr.1,hr.2,
    D.sourceOrbit_hermitian_ordinary_radical_fixed_residual_escape
      h hmany hV hnon d B eQ hfield hw K hK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
