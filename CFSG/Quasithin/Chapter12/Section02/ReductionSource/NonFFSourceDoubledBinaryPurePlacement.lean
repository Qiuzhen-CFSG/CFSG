module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPurePlacement
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Rigidity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureAction

/-!
# The original H1 component Sylow lies in the orbit centralizer core

The already constructed faithful sixteen supplies the concrete root and
multiplier calculations for every surviving component model. The result
centralizes the original order-thirty-two hyperplane upstairs in G.
E.3.6, with the proved value s=2, identifies its centralizer in T with
C_T(W), which is the original two-core of LT. The original component
Sylow, its canonical central quotient, both marked axes, and the same
minimal overgroup are retained. The actual component join with this core
has the core as a Sylow subgroup, even if the core permutes components.

The Cartan index is also retained on the same quotient Sylow; its ambient
normalizer placement and the selected-line contradiction remain to prove.
The earlier hypothesis w ≤ 1 remains explicit.
Source: Aschbacher–Smith, 7.7.3 H1 argument, printed p.706,
refs/quasithin.pdf; centralizer rigidity is E.3.6, printed p.232.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open DoubledBinaryLocalCore DoubledBinaryPurePlacement DoubledBinaryInnerAction
open DoubledBinaryPlanes DoubledBinaryIntersection BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every hyperplane of the original orbit has the same centralizer in T.
The global r bound and the non-FF local parameter discharge E.3.6. -/
theorem sourceOrbit_binary_hyperplane_centralizer_eq_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (B : Subgroup G) (hBW : B ≤ D.sourceOrbit)
    (hcorank : subgroupCorank D.sourceOrbit B = 1) :
    (T : Subgroup G) ⊓ centralizer (B : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  have hs := (D.sourceOrbit_binary_small_parameters h hd F hF hmodel hnon
    (le_trans (by decide) hr)).2.2.1
  have hc := centralizer_inf_eq_of_corank_lt_globalS hBW
    (by rw [hcorank,hs]; decide) T.isPGroup'
  rw [hc]
  simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h

/-- Root centralization, the genuine multiplier input, and hyperplane
rigidity place the SAME component Sylow in the original orbit core. -/
theorem sourceOrbit_binary_exists_pureLine_component_core_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        let C := centralizer (Z : Set G)
        let B := localBase L (T : Subgroup G) Z
        let Q₀ := (L ⊔ (T : Subgroup G)).pCoreIn 2
        Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ C ∧
        (∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = (T : Subgroup G) ⊓ C) ∧
        pPrimeCore 2 C = ⊥ ∧
        ∃ H : Subgroup G, B ≤ H ∧ H ≤ C ∧ ¬ HasCharacteristicTwo H ∧
          (∀ J : Subgroup G, B ≤ J → J < H → HasCharacteristicTwo J) ∧
          IsSQTK KnownSimple.IsKnownSimple H ∧
          HasCharacteristicTwo (H ⊓ normalizer (L : Set G) : Subgroup G) ∧
          pPrimeCore 2 H = ⊥ ∧ Z ≤ H.pCoreIn 2 ∧
          (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ C) ∧
          ∃ K : Subgroup G, IsComponentIn K H ∧ ¬ K ≤ normalizer (L : Set G) ∧
            H = K ⊔ B ∧
            Nat.card (D.sourceOrbit ⊓ centralizer (K : Set G) : Subgroup G) ≤ 4 ∧
            ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
              (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
              (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
              DoubledBinaryOmega.HasMarking D.sourceOrbit L E ∧
              (∀ w : Additive D.sourceOrbit, w ≠ 0 →
                (∃ P : Sylow 2 G,
                  (P : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) →
                (w.toMul : G) ∉ centralizer (K : Set G)) ∧
              (∀ w : Additive D.sourceOrbit, (w.toMul : G) ∈ centralizer (K : Set G) →
                ¬ DoubledBinaryComponentGeometry.IsSingular (E w)) ∧
              ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
                let U := ambientPlane D.sourceOrbit E v f
                let A := ⁅D.sourceOrbit,localResidual L U⁆
                Z ≤ U ∧ Disjoint U A ∧ Nat.card A = 16 ∧
                  A ≤ ⁅D.sourceOrbit,localResidual L Z⁆ ∧
                  Nat.card (Z ⊔ A : Subgroup G) = 32 ∧
                  ((T : Subgroup G) ⊓ C) ≤ normalizer ((Z ⊔ A : Subgroup G) : Set G) ∧
                  (∃ N : Subgroup ((T : Subgroup G) ⊓ C : Subgroup G), N.index ≤ 2 ∧
                    ⁅N.map ((T : Subgroup G) ⊓ C).subtype,Z ⊔ A⁆ ≤ Z) ∧
                  subgroupCorank D.sourceOrbit (Z ⊔ A) = 1 ∧
                  centralizer ((Z ⊔ A : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
                  ¬ A ≤ centralizer (K : Set G) ∧
                  ∃ hAN : A ≤ normalizer (K : Set G),
                    A ⊓ centralizer (K : Set G) = ⊥ ∧
                    (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                    (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                      (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                        K.normalizerMonoidHom (inclusion hAN a)) ∧
                      Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                      ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = K ⊓ ((T : Subgroup G) ⊓ C) ∧
                        let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                        j.range ≤ (Q : Subgroup _) ∧
                        (Q : Subgroup _) ≤ normalizer (j.range : Set (K ⧸ center K)) ∧
                        ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf (Q : Subgroup _)).index ≤ 2 ∧
                        ¬ IsCyclic (center Q) ∧
                        center K = ⊥ ∧
                        j.range ≤ (center Q).map (Q : Subgroup _).subtype ∧
                        6 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                          (normalizer (Q : Set (K ⧸ center K)))).index ∧
                        (P : Subgroup K).map K.subtype ≤ centralizer ((Z ⊔ A : Subgroup G) : Set G) ∧
                        (T : Subgroup G) ⊓ centralizer ((Z ⊔ A : Subgroup G) : Set G) = Q₀ ∧
                        (P : Subgroup K).map K.subtype ≤ Q₀ ∧
                        (∃ S : Sylow 2 (K ⊔ Q₀ : Subgroup G),
                          (S : Subgroup _).map (K ⊔ Q₀).subtype = Q₀)) ∧
                    4 ≤ primeRank 2 (K ⧸ center K) ∧
                    DoubledBinaryComponentModels.NonbinaryLieModel (K ⧸ center K) := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,hPC,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hPH,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,
    hnorm,hN,hcorank,hCM,hact,hAN,hker,hi,
    ⟨j,hj,hjact,hjcard,hje,P,hPactual,hAQ,hQN,hindex,hcyc⟩,hrank,hmodelK⟩ :=
    D.sourceOrbit_binary_exists_pureLine_component_sylow_action h hd F hF hmodel hnon hw
  let W₀ := D.sourceOrbit
  let Z := ⁅offenderNormalizer W₀ g,offenderFixedSpan W₀ g⁆
  let C := centralizer (Z : Set G)
  let B := localBase L (T : Subgroup G) Z
  let Q₀ := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := ambientPlane W₀ E v f
  let A := ⁅W₀,localResidual L U⁆
  let := hje
  obtain ⟨hzK,hPjoin,hjcent,hlarge⟩ := original_sylow_centralizes_join H K Z A
    hK hoddH (hK.1.trans hHC) hmodelK hAN j hjact hjcard P hAQ hindex
  have hZW : Z ≤ W₀ := hpair.trans inf_le_left
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans hmark.1))
  have hQ : (T : Subgroup G) ⊓ centralizer ((Z ⊔ A : Subgroup G) : Set G) = Q₀ :=
    D.sourceOrbit_binary_hyperplane_centralizer_eq_core h hd F hF hmodel hnon
      (Z ⊔ A) (sup_le hZW hAW) hcorank
  have hPT : (P : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    rw [hPactual]
    exact inf_le_right.trans inf_le_left
  have hPQ : (P : Subgroup K).map K.subtype ≤ Q₀ := by
    rw [←hQ]
    exact le_inf hPT hPjoin
  have hQH : Q₀ ≤ H := by
    have hQW : (T : Subgroup G) ⊓ centralizer (W₀ : Set G) = Q₀ := by
      simpa only [W₀,Q₀,D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
    rw [←hQW]
    exact (inf_le_inf_left _ (centralizer_le hZW)).trans (le_sup_right.trans hBH)
  obtain ⟨S,hS⟩ := DoubledBinaryCoverPlacement.core_sylow_join H K Q₀ hK hQH
    (isPGroup_pCoreIn 2 _) P hPQ
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,hPC,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hPH,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,
    hnorm,hN,hcorank,hCM,hact,hAN,hker,hi,
    ⟨j,hj,hjact,hjcard,hje,P,hPactual,hAQ,hQN,hindex,hcyc,hzK,hjcent,hlarge,
      hPjoin,hQ,hPQ,⟨S,hS⟩⟩,hrank,hmodelK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
