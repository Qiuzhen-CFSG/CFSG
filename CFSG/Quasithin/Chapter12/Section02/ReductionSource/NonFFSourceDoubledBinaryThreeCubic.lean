module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryThreeCore
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeCubic

/-!
# One cubic factor on the original radical modulo the chosen orbit

The original local residual has cubic quotient over its two-core; Cauchy's
theorem supplies an actual subgroup A of order three inside that residual.
The compatible binary-three quotient and whole commutator-core recognition
give cubic lengths two on O₂(H) and three on the original radical Q.
The original natural--dual orbit W has length two for that same A.

The source centralizer identity makes W central in Q, and coprime lifting
gives length one and fixed index four on the literal Q/W conjugation action.
Both marked seed planes and the original conjugator survive the application;
no cubic, factor count, core equality or quotient-action premise is added.
The graph-automorphism contradiction, paired-plane containment and remaining
non-FF doubled branches are still required for the full task.

Source: Aschbacher--Smith, final paragraph of the proof of 7.7.3,
printed p.709, refs/quasithin.pdf. W is the full source orbit (the book's V),
not the chosen irreducible subgroup V of Chapter12.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open NoncentralChiefRefinement.CubicComparison DoubledBinaryThreeCubic
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Select the original cubic and prove fixed index four on the literal Q/W,
retaining both seed markings and adding no source hypothesis. -/
theorem sourceOrbit_binary_pairedPlane_cubic_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          HasMarking D.sourceOrbit L E ∧
          let U := ambientPlane D.sourceOrbit E v f
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H C₀ A : Subgroup G,
              H ∈ Chapter3.HStar (localBase L (T : Subgroup G) U) (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ H = C₀ ⊔ Q ∧
              DoubledBinaryThreeCore.WholeCoreConclusion KnownSimple.IsKnownSimple C₀ Q ∧
              Nat.card A = 3 ∧ A ≤ localResidual L U ∧ A ≤ C₀ ∧
              conjugationCubicLength A (H.pCoreIn 2) = 2 ∧
              conjugationCubicLength A Q = 3 ∧
              conjugationCubicLength A D.sourceOrbit = 2 ∧
              D.sourceOrbit ≤ Q ∧
              ∃ (hAQ : A ≤ normalizer (Q : Set G))
                (hAW : A ≤ normalizer (D.sourceOrbit : Set G))
                (hWN : (D.sourceOrbit.subgroupOf Q).Normal),
                letI := hWN
                letI := quotientConjugationAction A Q D.sourceOrbit hAQ hAW
                sectionCubicLength A D.sourceOrbit Q = 1 ∧
                FixedPoints.cubicLength A (Q ⧸ D.sourceOrbit.subgroupOf Q) = 1 ∧
                (FixedPoints.subgroup A (Q ⧸ D.sourceOrbit.subgroupOf Q)).index = 4) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_whole_core h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,
    hnoSix,hnoSevenStar,hnoG2Star,hWstar,hdis,hcard,hmodels,hker,he,
    ⟨S,hS,hSR,hflags⟩,hnoFive,hkernel,hoffender,hthompson,hproper,hCJ,c,hm,hcon,
    hnoFiveStar,hnoFourStar,hremaining,hthree,hfull,hHjoin,hstarKernel,hcenterH,
    hwhole,hel,hc64⟩ := hescape hout
  let U := ambientPlane D.sourceOrbit E v f
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C₀ := C.map H.subtype
  let B := localBase L (T : Subgroup G) U
  let R0 := localResidual L U
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R0 ≤ H := le_sup_left.trans hBH
  have hRC : R0 ≤ C₀ := by
    intro r hr
    exact ⟨⟨r,hRH hr⟩,hAC hr,rfl⟩
  have hPB : (P : Subgroup H) ≤ B.subgroupOf H := by
    intro p hp
    exact (show (T : Subgroup G) ⊓ centralizer (U : Set G) ≤ B from le_sup_right)
      (hP ▸ mem_map_of_mem H.subtype hp)
  obtain ⟨hLN,k,hks,a,hE,ha,hcov⟩ := hmark
  obtain ⟨seed⟩ := hmodel
  let model := seed.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv
  have hseed : (centralizer (V : Set G)).subgroupOf L = pCore 2 L :=
    D.seedComparison.centralizer_eq_twoCore
      (D.seedComparison.projection_injective_of_linearThree h.quasisimple model)
  have hVW : V ≤ D.sourceOrbit := by rw [D.sourceOrbit_eq]; exact le_componentOrbit _ _
  have hk2 : IsPGroup 2 k.ker := by
    apply (pCore_isPGroup (p := 2) (G := L)).to_le
    intro l hl
    rw [←hseed]
    apply centralizer_le hVW
    intro w hw
    have hew := hE l (Additive.ofMul ⟨w,hw⟩)
    rw [show k l = 1 from hl,NaturalDual.action.map_one] at hew
    have heq := E.injective hew
    have hc : (l : G) * w * (l : G)⁻¹ = w := congrArg (fun x : Additive D.sourceOrbit => (x.toMul : G)) heq
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  let J0 := L ⊓ centralizer (U : Set G)
  obtain ⟨πL,hπL,hkL⟩ := DoubledBinaryResidualMovement.localBase_quotient
    D.sourceOrbit L J0 hLN k hks E hE a ha hcov v f hfv (inf_le_left.trans hLN) inf_le_right le_rfl
  have hπkernel : IsPGroup 2 πL.ker := by
    apply (pCore_isPGroup.comap_of_injective (inclusion (show J0 ≤ L from inf_le_left))
      (inclusion_injective _)).to_le
    intro x hx
    rw [hkL] at hx
    change inclusion (show J0 ≤ L from inf_le_left) x ∈ pCore 2 L
    rw [←hseed]
    exact centralizer_le hVW hx
  have hcJ := DoubledBinaryResidualMovement.residual_cubic_quotient πL hπL hπkernel
  have hd3 : 3 ∣ Nat.card (pResidual 2 J0) := by
    rw [←hcJ]
    exact (pCore 2 (pResidual 2 J0)).index_dvd_card
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := pResidual 2 J0) 3 hd3
  let j := J0.subtype.comp (pResidual 2 J0).subtype
  let A := (zpowers x).map j
  have hj : Function.Injective j := J0.subtype_injective.comp (pResidual 2 J0).subtype_injective
  have hA : Nat.card A = 3 := by rw [card_map_of_injective hj,Nat.card_zpowers,hx]
  have hAR : A ≤ R0 := by
    rintro _ ⟨y,hy,rfl⟩
    exact mem_map_of_mem J0.subtype y.property
  have hAL : A ≤ L := hAR.trans ((map_subtype_le _).trans inf_le_left)
  have hAH : A ≤ H := hAR.trans hRH
  have hAcore := (ambient_core_cubic_length hwhole A hA (hAR.trans hRC)).2
  rw [←hHjoin] at hAcore
  have horbit := orbit_cubic_length D.sourceOrbit L A hLN k hk2 hA hAL E hE
  obtain ⟨e0,hn,b0,i0,hs0,hbase0,hpre0,hin0,hgen0,hgenQ,π,hπ,hπker,hπC,
    hπQ,hpreQ,hindexQ,hindexB⟩ := hfull
  have hBeq : (R0.subgroupOf H) ⊔
      (((T : Subgroup G) ⊓ centralizer (U : Set G)).subgroupOf H) = B.subgroupOf H := by
    rw [←subgroupOf_sup hRH (le_sup_right.trans hBH)]
    rfl
  rw [hBeq] at hindexB
  have hQeq : (B.subgroupOf H).pCoreIn 2 = Q.subgroupOf H := by
    rw [pCoreIn_subgroupOf 2 B H hBH]
    exact congrArg (fun X : Subgroup G => X.subgroupOf H) hcore
  have hAc : Nat.card (A.subgroupOf H) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA
  have hcoreH : conjugationCubicLength (A.subgroupOf H) (pCore 2 H) = 2 := by
    rw [←length_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hAH]
    exact hAcore
  have hrad := radical_cubic_length π hπ hπker P (B.subgroupOf H) (Q.subgroupOf H)
    hPB hindexB hQeq hπQ (A.subgroupOf H) hAc
    (subgroupOf_mono H (hAR.trans le_sup_left)) hcoreH
  rw [length_subgroupOf A Q H hAH hi.setup.radical_le] at hrad
  have hQC : Q ≤ centralizer (D.sourceOrbit : Set G) := by
    have hh := D.doubledOrbit_sylow_centralizer h
    rw [←D.sourceOrbit_eq] at hh
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    rw [←hh]
    exact inf_le_right
  have hWQ : D.sourceOrbit ≤ Q := (D.sourceOrbit_core_normalizer h).1
  have hAQ : A ≤ normalizer (Q : Set G) := by
    change A ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)
    rw [←hcore]
    exact (hAR.trans le_sup_left).trans (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hAW : A ≤ normalizer (D.sourceOrbit : Set G) := hAL.trans hLN
  let hWN : (D.sourceOrbit.subgroupOf Q).Normal :=
    normal_subgroupOf_of_le_normalizer (hQC.trans (Subgroup.centralizer_le_normalizer _))
  have hquot := quotient_cubic_length A D.sourceOrbit Q hA
    (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))) hWQ hAQ hAW hrad horbit
  exact ⟨H,C₀,A,hH,hHC,hHjoin,hwhole,hA,hAR,hAR.trans hRC,hAcore,hrad,horbit,
    hWQ,hAQ,hAW,hWN,hquot⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
