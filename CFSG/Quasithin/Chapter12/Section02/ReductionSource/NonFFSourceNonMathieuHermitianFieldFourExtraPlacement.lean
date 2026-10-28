module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourExtraParabolic

/-!
# Actual H-star placement and extraspecial centers on the Hermitian tensor

For the original R = N_L(U)^∞ and X = Ξ_p(K), the literal radical
commutator identity supplies a nontrivial perfect plane action. R normalizes
the original chosen orbit. The extraspecial center argument therefore puts
XT in the actual H-star family, using the already proved Hermitian exclusion
of the module from an H-star two-core.

The final application removes the H-star premise from the earlier center
placement theorem on both weak-closure branches. It also identifies the
intrinsic maximal subgroup XT intersect N_G(R) with XT intersect M. Every
actual odd Sylow supplement center lies in M intersect C_G(V), has order p,
and has an escaping normalizer whose full odd core lies in M.

The normalizer's containment in M is not asserted: whole odd-normalizer
control, nilpotent exclusion, quasisimplicity and the remainder of 8.2.8--13
still require proofs. All kernels, the original Sylow, action and marked
four-space are retained.

Source: Aschbacher--Smith 8.2.2(1), 8.2.7 and B.6.8(2), printed
pp.714,717--718,113--114, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original extraspecial radical join is in H-star, with no placement
premise. The original module's core exclusion discharges minimality. -/
theorem sourceOrbit_hermitian_extraspecial_radical_hstar
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (U K : Subgroup G) [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hu : rank U = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : Chapter8.Section02.Normalizer.localResidual L U ≤ K)
    (hR : Nonempty (((Chapter8.Section02.Normalizer.localResidual L U) ⧸
      pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)) ≃* SL(2,E 1)))
    (p : ℕ) [Fact p.Prime]
    (hnil : Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)))
    (hx : IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K)))
    (hc : Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K)) = p^3) :
    Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
      Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
  obtain ⟨hXi,_,hout,_⟩ := D.sourceOrbit_hermitian_nilpotent_radical_centralizer
    h.toHypothesis1221 U K hUV hu hTU hKU hK hTK hRK hR p hnil hd
  have hUne : U ≠ ⊥ := by
    intro hz
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hK.subgroupOf_of_le le_sup_left (sup_le hKU hTU),?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · exact ne_bot_of_le_ne_bot hUne
        (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
          (hUV.trans (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right))
          (sup_le hKU hTU))
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hp := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let H := L ⊓ normalizer (U : Set G)
  let er : solvableResidual H ≃* R :=
    (solvableResidual H).equivMapOfInjective H.subtype H.subtype_injective
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := er.toMonoidHom) er.surjective
  let : IsSimpleGroup PSL(2,E 1) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [card_E]; norm_num)
  let : IsSimpleGroup SL(2,E 1) := (Theory.PSL2.sl2QuotientEquiv (E 1)).isSimpleGroup
  let : IsSimpleGroup (R ⧸ pCore 2 R) := hR.some.isSimpleGroup
  have hns : ¬ Group.IsSolvable R := by
    intro hsol
    let := hsol
    exact Group.IsPerfect.not_isSolvable (R ⧸ pCore 2 R) inferInstance
  have hTR := Chapter8.Section02.Normalizer.normalizes_localResidual L U T
    D.sylow_normalizes_component hTU
  have hcomm := Chapter1.RadicalActions.XiP_commutator_eq_of_nonsolvable_subgroup_of_A36
    hA36 hlocal hQ (nilpotent_not_quasisimple hnil) hTK hTR hRK hns ho hd
  let := hx
  exact extraspecial_radical_join_HStar T hXi
    (hRK.trans (Chapter1.XiP_invariant p K.le_normalizer))
    (((Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_left).trans
      D.sourceOrbit_component_normalizes) hcomm hout
    D.sourceOrbit_weakClosure_setup.le_sylow D.sourceOrbit_weakClosure_setup.normalizes
    (fun _ hJ => D.sourceOrbit_hermitian_not_le_HStar_core h hs hrow hJ) ho hc

/-- The literal tensor supplies H-star placement and the actual centers on both branches. -/
theorem sourceOrbit_hermitian_tensor_nilpotent_centers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 ∧
      ∃ U : Subgroup G, ∃ hU : IsElementaryAbelian 2 U, letI := hU
        U ≤ D.sourceOrbit ∧ rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        let R := Chapter8.Section02.Normalizer.localResidual L U
        R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
        Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
          R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          ¬ Chapter1.Section02.A36Natural (Chapter1.XiQuotient K) ∧
          (Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K) →
            ∀ (p : ℕ) (_ : Fact p.Prime),
              p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)) →
              Chapter1.Section02.LocalModels.OddExtraspecialThree p
                (pCore p (Chapter1.XiQuotient K)) ∧
              IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K)) ∧
              Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K)) = p^3 ∧
              Monoid.exponent (Chapter1.XiQuotient (Chapter1.XiP p K)) = p ∧
              (Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
                Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
                (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (R : Set G) =
                  (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (L : Set G) ∧
                ∀ P : Sylow p (Chapter1.XiP p K),
                  let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
                  let Z := (center Y).map Y.subtype
                  Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
                    Z ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
                    ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G) ∧
                    (pPrimeCore 2 (normalizer (Z : Set G))).map (normalizer (Z : Set G)).subtype ≤
                      normalizer (L : Set G))) := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,hcores⟩ :=
    D.sourceOrbit_hermitian_tensor_nilpotent_centers_of_hstar
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  let := hU
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  refine ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,?_⟩
  intro hnil p hp hd
  let := hp
  obtain ⟨hfull,hx,hcard,hexp,hcenters⟩ := hcores hnil p hp hd
  have hH := D.sourceOrbit_hermitian_extraspecial_radical_hstar h hs hrow
    U K hUV hu hTU hKU hK (hTU.trans hNK) hRK hR p hnil hd hx hcard
  obtain ⟨_,hTB,hcov,_⟩ := D.sourceOrbit_hermitian_extraspecial_radical_parabolic
    h.toHypothesis1221 U K hUV hu hTU hKU hK (hTU.trans hNK) hRK hR p hnil hd hx
  have heq := (Chapter3.HStar.unique_maximal T D.sylow_normalizes_component hH).2.2
    _ hTB hcov
  exact ⟨hfull,hx,hcard,hexp,hH,heq,hcenters hH⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
