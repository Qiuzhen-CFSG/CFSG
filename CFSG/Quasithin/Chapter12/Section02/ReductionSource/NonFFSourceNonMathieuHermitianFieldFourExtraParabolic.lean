module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraParabolic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourExtraCenter

/-!
# The original extraspecial radical's intrinsic minimal parabolic

The literal residual R = N_L(U)^∞ has its retained SL₂(4) quotient.
Its relative normality and the radical commutator identity force X = Ξ_p(K)
outside N_G(R), as well as outside the original M. Every proper overgroup
of the original Sylow in XT normalizes R. Hence XT is intrinsically a
minimal parabolic, whose unique maximal overgroup is XT intersect N_G(R).
The full center preimage and every actual extraspecial Sylow center lie
in that normalizer, with the original two-core retained.

The tensor application constructs the same four-space and containing
normal component on both weak-closure branches. It preserves the full
kernel and the earlier natural and elementary-radical exclusions.
The comparison XT intersect N_G(R) <= M, H-star placement, whole odd
normalizer control, quasisimplicity and 8.2.8--13 remain open. Intrinsic
minimal-parabolic status is not being substituted for H-star membership.

Source: Aschbacher--Smith 1.3.1--3, B.6.1 and 8.2.7,
printed pp.508--509,112,717--718, refs/quasithin.pdf (1 March 2004).
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

/-- The actual nilpotent extraspecial radical join is a minimal parabolic,
with its unique maximal overgroup identified by the original residual. -/
theorem sourceOrbit_hermitian_extraspecial_radical_parabolic
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
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
    (hx : IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K))) :
    let X := Chapter1.XiP p K
    let H := X ⊔ (T : Subgroup G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    ChapterB.IsMinimalParabolicOver T H ∧
      (T : Subgroup G) ≤ H ⊓ normalizer (R : Set G) ∧
      H ⊓ normalizer (R : Set G) ⋖ H ∧
      (∀ J : Subgroup G, (T : Subgroup G) ≤ J → J < H →
        J ≤ H ⊓ normalizer (R : Set G)) ∧
      radicalCenterPreimage X ≤ normalizer (R : Set G) ∧
      ∀ P : Sylow p X,
        let Y := (P : Subgroup X).map X.subtype
        (center Y).map Y.subtype ≤ normalizer (R : Set G) := by
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
  obtain ⟨hp,hq,hXi⟩ := nilpotent_radical_member hA36 hlocal hQ hTK p hnil hd
  have hn := nilpotent_not_quasisimple hnil
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
  have hTR := Chapter8.Section02.Normalizer.normalizes_localResidual L U T
    D.sylow_normalizes_component hTU

  have houtR := radical_not_le_relative_normalizer hA36 hlocal hQ hTK hTR hRK hKU
    (show normalizer (R : Set G) ⊓ normalizer (U : Set G) ≤ normalizer (R : Set G)
      from inf_le_left) hn ho hd hXi
  let := hx
  have hRX : R ≤ normalizer (Chapter1.XiP p K : Set G) :=
    hRK.trans (Chapter1.XiP_invariant p K.le_normalizer)
  obtain ⟨hP,hTB,hcov,hproper⟩ := extraspecial_radical_parabolic_at_residual
    (p := p) T hXi hRX hTR houtR
  have hc := hXi.pCoreIn_le_of_isSylowIn
    (show Chapter1.IsSylowIn 2 (T : Subgroup G)
      (Chapter1.XiP p K ⊔ (T : Subgroup G)) from
      ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩)
  let : IsCyclic (center (Chapter1.XiQuotient (Chapter1.XiP p K))) :=
    isCyclic_of_prime_card (IsExtraspecial.center_order_p p _)
  have hz := radicalCenterPreimage_normalizes (Chapter1.XiP p K) R hRX (hc.trans hTR)
  refine ⟨hP,hTB,hcov,hproper,hz,?_⟩
  intro P
  let X := Chapter1.XiP p K
  let Y := (P : Subgroup X).map X.subtype
  let e := hXi.ambientSylowQuotientEquiv ho hq P
  change (center Y).map Y.subtype ≤ normalizer (R : Set G)
  rintro z ⟨y,hy,rfl⟩
  apply hz
  refine ⟨inclusion (map_subtype_le (P : Subgroup X)) y,?_,rfl⟩
  change e y ∈ center (Chapter1.XiQuotient X)
  exact (Subgroup.centerCongr e ⟨y,hy⟩).property

/-- On the literal tensor, construct the same original four-space and residual
and prove intrinsic minimal-parabolic status for every remaining radical join.
The actual supplement centers normalize that original residual. -/
theorem sourceOrbit_hermitian_tensor_extraspecial_parabolics
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
              let X := Chapter1.XiP p K
              IsExtraspecial p (Chapter1.XiQuotient X) ∧
              Nat.card (Chapter1.XiQuotient X) = p^3 ∧
              Monoid.exponent (Chapter1.XiQuotient X) = p ∧
              ChapterB.IsMinimalParabolicOver T (X ⊔ (T : Subgroup G)) ∧
              (T : Subgroup G) ≤ (X ⊔ (T : Subgroup G)) ⊓ normalizer (R : Set G) ∧
              (X ⊔ (T : Subgroup G)) ⊓ normalizer (R : Set G) ⋖ X ⊔ (T : Subgroup G) ∧
              (∀ J : Subgroup G, (T : Subgroup G) ≤ J → J < X ⊔ (T : Subgroup G) →
                J ≤ (X ⊔ (T : Subgroup G)) ⊓ normalizer (R : Set G)) ∧
              radicalCenterPreimage X ≤ normalizer (R : Set G) ∧
              X ≤ centralizer (U : Set G) ∧ ¬ X ≤ normalizer (L : Set G) ∧
              ∀ P : Sylow p X,
                let Y := (P : Subgroup X).map X.subtype
                let Z := (center Y).map Y.subtype
                Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
                  Z ≤ centralizer (U : Set G) ⊓ normalizer (R : Set G) ∧
                  ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G)) := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,hcores⟩ :=
    D.sourceOrbit_hermitian_tensor_nilpotent_centralizers
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  let := hU
  refine ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,?_⟩
  intro hnil p hp hd
  let := hp
  obtain ⟨hfull,hx,hcard,hexp,hcent,hout,hSyl⟩ := hcores hnil p hp hd
  obtain ⟨hP,hTB,hcov,hproper,hpre,hcenters⟩ :=
    D.sourceOrbit_hermitian_extraspecial_radical_parabolic h.toHypothesis1221
      U K hUV hu hTU hKU hK (hTU.trans hNK) hRK hR p hnil hd hx
  refine ⟨hfull,hx,hcard,hexp,hP,hTB,hcov,hproper,hpre,hcent,hout,?_⟩
  intro P
  obtain ⟨_,_,_,_,_,hc,hcyc,hne,hZU,_,hescape⟩ := hSyl P
  exact ⟨hc,hcyc,hne,le_inf hZU (hcenters P),hescape⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
