module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureComponentSylow
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureFaithful

/-!
# The nonbinary component reduction at the original offender line

For the same offender, pure line and minimal H1 component, C_T(Z)
normalizes the actual order-thirty-two join and has a subgroup of index
at most two centralizing that join modulo Z. The faithful plane actor
then embeds as a normal elementary sixteen in the literal component
Sylow image under K → K/Z(K), with centralizer index at most two.

Its Sylow center is noncyclic. Together with the existing rank-four
bound, the proved component catalogue forces the same K/Z(K) onto the
nonbinary Lie list. The hypothesis w ≤ 1 remains explicit; the root,
central-cover and Cartan exclusions and the other doubled rows remain.
Source: Aschbacher–Smith, the H1 argument in 7.7.3, printed p.706,
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open DoubledBinaryLocalCore DoubledBinaryPureAction DoubledBinaryPureComponentSylow DoubledBinaryInnerAction
open DoubledBinaryPlanes DoubledBinaryIntersection BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original offender and minimal H1 component have the literal Sylow
image restrictions needed for the nonbinary Lie reduction. -/
theorem sourceOrbit_binary_exists_pureLine_component_sylow_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        let C := centralizer (Z : Set G)
        let B := localBase L (T : Subgroup G) Z
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
                        ¬ IsCyclic (center Q)) ∧
                    4 ≤ primeRank 2 (K ⧸ center K) ∧
                    DoubledBinaryComponentModels.NonbinaryLieModel (K ⧸ center K) := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨PC,hPC⟩,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,⟨PH,hPH⟩,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,hcorank,hCM,hact,
    hAN,hker,hi,⟨j,hj,hjact⟩,hrank⟩ :=
    D.sourceOrbit_binary_exists_pureLine_faithful_component_action h hd F hF hmodel hnon hw
  let W₀ := D.sourceOrbit
  let Z := ⁅offenderNormalizer W₀ g,offenderFixedSpan W₀ g⁆
  let C := centralizer (Z : Set G)
  let S₀ := (T : Subgroup G) ⊓ C
  let U := ambientPlane W₀ E v f
  let A := ⁅W₀,localResidual L U⁆
  have hZW : Z ≤ W₀ := hpair.trans inf_le_left
  obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
  have hp : (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).1 = 0) := by
    rcases hpure with hh | hh
    · exact Or.inl (fun w hw => (hV w).mpr (hh hw))
    · exact Or.inr (fun w hw => (hVt w).mpr (hh hw))
  have hR : localResidual L Z ≤ normalizer (W₀ : Set G) ⊓ C :=
    (map_subtype_le _).trans (inf_le_inf_right (C) hLN)
  have hS₀ : S₀ ≤ normalizer (W₀ : Set G) ⊓ C :=
    le_inf (inf_le_left.trans D.sourceOrbit_weakClosure_setup.normalizes) inf_le_right
  have hpS : IsPGroup 2 S₀ := T.isPGroup'.to_le inf_le_left
  obtain ⟨hnorm,N,hN,hcomm⟩ := pureLine_sylow_modulo W₀ Z (localResidual L Z) S₀ A
    E a hcov hZW hZ hp hR hS₀ hpS hmove hhyper
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans hLN))
  have hAS : A ≤ S₀ := le_inf (hAW.trans D.sourceOrbit_weakClosure_setup.le_sylow)
    (hAW.trans ((le_centralizer W₀).trans (centralizer_le hZW)))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  obtain ⟨PK,hPK⟩ := PH.exists_subgroupOf_eq_of_subnormal (K.subgroupOf H) hK.2.1
  let e := subgroupOfEquivOfLe hK.1
  let P := PK.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPS : (P : Subgroup K).map K.subtype ≤ S₀ := by
    rintro _ ⟨k,hk,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hk
    have hxP : (x.val : H) ∈ (PH : Subgroup H) := by
      rw [hPK] at hx
      exact hx
    have hh := mem_map_of_mem H.subtype hxP
    rw [hPH] at hh
    exact hh
  have hPactual : (P : Subgroup K).map K.subtype = K ⊓ S₀ := by
    have hle : (P : Subgroup K) ≤ S₀.subgroupOf K := by
      intro k hk
      exact hPS (mem_map_of_mem K.subtype hk)
    have he := P.is_maximal' hpS.comap_subtype hle
    rw [←he,map_comap_eq,range_subtype,inf_comm]
  have hZK : Z ≤ centralizer (K : Set G) := le_centralizer_iff.mpr (hK.1.trans hHC)
  obtain ⟨hAQ,hQN,hindex⟩ := projected_sylow_modulo K Z A S₀ hAS hpS hAN hZK
    hnorm N hN hcomm P hPS j hjact
  have hjcard : Nat.card j.range = 16 :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hcard
  let hje : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_surjective
    j.rangeRestrict j.rangeRestrict_surjective
  have hcyc := projected_center_not_cyclic
    (P.mapSurjective (QuotientGroup.mk'_surjective (center K))) j.range hjcard hAQ hQN hindex
  have hmodelK := DoubledBinaryComponentModels.component_nonbinary H K hSQ hK hrank ⟨_,hcyc⟩
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨PC,hPC⟩,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,⟨PH,hPH⟩,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,⟨hLN,q,hq,a,hE,ha,hcov⟩,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,
    hnorm,⟨N,hN,hcomm⟩,hcorank,hCM,hact,hAN,hker,hi,
    ⟨j,hj,hjact,hjcard,hje,P,hPactual,hAQ,hQN,hindex,hcyc⟩,hrank,hmodelK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

