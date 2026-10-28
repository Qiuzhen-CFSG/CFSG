module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourResidualSeed
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianAmbientModels
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianAmbientAction
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank

/-!
# The actual odd actor on the ambient Hermitian comparison component

Retain the original ordinary J₄ cover, both original involutions and the
full M₂₂ seed in their paired centralizer. Its containing normal component
Q in C_G(z) has simple section M₂₂, M₂₃, M₂₄, HS or J₄. The original
actor of prime greater than three acts by inner automorphisms on the full
quasisimple quotient Q/O₂(Q), with its center retained.

The native escape from N_G(L) forces a nontrivial simple-section action
of exact order p. Indeed, a trivial action would descend to the two-core
commutator bound and the original odd-actor closure comparison would place
Q in N_G(L). These assertions use the same Q and original A and T.
The remaining step is to exclude this nontrivial inner action; no
centralization of the full paired seed by A is assumed here.

Source: the ordinary comparison needed for Aschbacher--Smith 4.4.3 and
Remark 4.4.2, printed pp.619--623, as applied in 8.2.7, p.718,
refs/quasithin.pdf. Whole odd-normalizer control and the subsequent
8.2.7--13 assembly remain with this source argument.
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
open Chapter8.Section02.HermitianSource Chapter7.NormalizedSource
open Chapter4.Section04.OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- On the same escaping ambient component, the original noncubic actor
induces inner automorphisms of the full quasisimple two-core quotient. -/
theorem sourceOrbit_hermitian_oddActor_ambient_inner_action
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
      ∃ K : Subgroup H, IsComponent H K ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ∃ (r : G) (z : K),
          r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
          ((z : H) : G) ∈ D.sourceOrbit ∧ orderOf z = 2 ∧
          (T : Subgroup G) ≤ centralizer ({((z : H) : G)} : Set G) ∧
          K.map H.subtype ≤ centralizer ({r} : Set G) ∧
          J.pCoreIn 2 ≤ centralizer ({r} : Set G) ⊓ centralizer ({((z : H) : G)} : Set G) ∧
          let C := centralizer ({((z : H) : G)} : Set G)
          let E := C ⊓ centralizer ({r} : Set G)
          let S := ((solvableResidual (centralizer ({z} : Set K))).map
            (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype)
          ∃ P : Subgroup E, P.IsCComponent ∧ P.Normal ∧
            Nonempty ((P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) ∧ P.map E.subtype = S ∧
            ∃ Q : Subgroup C, Q.IsCComponent ∧ ∃ hnQ : Q.Normal,
              letI := hnQ
              IsQuasisimple (Q ⧸ pCore 2 Q) ∧
              P.map (inclusion inf_le_left) ≤ Q ∧ S ≤ Q.map C.subtype ∧
              (T : Subgroup G) ≤ normalizer (Q.map C.subtype : Set G) ∧
              ∃ hAC : A ≤ C, A ≤ normalizer (Q.map C.subtype : Set G) ∧
              ¬ S ≤ normalizer (L : Set G) ∧ ¬ Q.map C.subtype ≤ normalizer (L : Set G) ∧
              (Nonempty (SimpleSection Q ≃* Sporadic.Mathieu.M22) ∨
                Nonempty (SimpleSection Q ≃* Sporadic.Mathieu.M23) ∨
                Nonempty (SimpleSection Q ≃* Sporadic.Mathieu.M24) ∨
                Nonempty (SimpleSection Q ≃* Sporadic.LeechRelated.HS.Carrier) ∨
                Nonempty (SimpleSection Q ≃* Janko4.Model)) ∧
              (∀ a : A, ∃ q : Q, quotientAut (pCore 2 Q)
                (MulAut.conjNormal (inclusion hAC a)) =
                  MulAut.conj (QuotientGroup.mk' (pCore 2 Q) q)) ∧
              ∃ a : A, orderOf (simpleAction Q (inclusion hAC a)) = p := by
  obtain ⟨J,H,W,hw,K,hK,heK,r,z,hr,hRr,hr2,hzV,hz,hTz,hKr,hRpair,
    P,hP,hnP,heP,hmP,Q,hQ,hnQ,hq,hPQ,hSQ,hTQ,hAC,hAQ,hSout,hQout⟩ :=
    D.sourceOrbit_hermitian_oddActor_ambient_residual_component
      h hmany hV hnon d B eQ hfield hp hgt A hne hAe hA hout
  let C := centralizer ({((z : H) : G)} : Set G)
  let E := C ⊓ centralizer ({r} : Set G)
  let := hnQ
  let := hq
  let := hP.perfect
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hP.ne_bot
  have hzG : orderOf (((z : H) : G)) = 2 := (orderOf_coe (z : H)).trans ((orderOf_coe z).trans hz)
  have hzne : ((z : H) : G) ≠ 1 := by intro he; rw [he,orderOf_one] at hzG; omega
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers (((z : H) : G)),fun hb => hzne (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hzG).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers (((z : H) : G))) = 2^1 by
      rw [Nat.card_zpowers,hzG]; rfl)
  have hE : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show E ≤ C from inf_le_left))).mp
      (hC.subgroup (E.subgroupOf C))
  let : IsQuasisimple (P ⧸ pCore 2 P) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hE hP
      (mathieu_radical_three_rank heP.some)
  let j := seedInclusion inf_le_left hPQ
  let f := (projection Q).comp j
  have hj := seedInclusion_injective inf_le_left hPQ
  obtain ⟨hfn,_,⟨ef⟩⟩ := seed_image j hj heP.some
  have hm := hermitian_seed_simple_section_models (simpleSection_model (hC.subgroup Q)) f hfn ef
  refine ⟨J,H,W,hw,K,hK,heK,r,z,hr,hRr,hr2,hzV,hz,hTz,hKr,hRpair,
    P,hP,hnP,heP,hmP,Q,hQ,hnQ,hq,hPQ,hSQ,hTQ,hAC,hAQ,hSout,hQout,hm,?_⟩
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  constructor
  · intro a
    apply hermitian_seed_odd_twoCore_action_inner (hC.subgroup Q) j hj heP.some _
      (hp.odd_of_ne_two (by omega) : Odd p)
    rw [←map_pow]
    have ha : (inclusion hAC a)^p=1 := by
      rw [←map_pow]
      have ha' : a^p=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
      rw [ha',map_one]
    rw [ha,map_one]
  · exact D.sourceOrbit_hermitian_oddActor_nontrivial_simple_action h.toHypothesis1221 hp hgt
      A hne hAe (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer
        h.toHypothesis1221 hV)) C Q hTQ hAC hAQ hQout

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
