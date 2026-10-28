module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourTensor
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourComponentOrder
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.CommutingRank
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
/-!
# The original Hermitian component's quintic action

The half-field tensor supplies the selected pair, its full quotient action,
and the same normal containing component K. Quasisimplicity makes K commute
with I modulo O₂(K). The source residual-product identity then makes K act
on the literal P/U. In the quintic branch, its original residual rotation
constructs sixteen-element scalars and the two-dimensional determinant-one
action, retaining the full commutator kernel and restricted kernel O₂(R).
The simultaneous action on U bounds the common simple quotient by 240.
The original residual's SL₂(4) quotient has order 60, so perfectness and
its original Sylow normalization prove R=K. Every new premise is discharged
here from the actual chosen module. In the cubic branch, the actual
SQTK normalizer and commuting S₃ section give m₃(K) ≤ 1.

Positive weak closure remains explicit. The cubic comparison R=K, zero-closure
exclusion and the remaining 8.2.9–13 stay with the final contradiction.
Source: Aschbacher–Smith 8.2.8(1), printed p.719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The actual quintic branch constructs the containing component's F₁₆-plane action and proves R=K, with the original scalar rotation and full kernels. -/
theorem sourceOrbit_hermitian_tensor_selected_component_action
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
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : 0 < globalW D.sourceOrbit T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        let U := D.sourceOrbit ⊓ centralizer
          (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
        let R := Chapter8.Section02.Normalizer.localResidual L U
        rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
          U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
          R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
          Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
          ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
            (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
            R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
            IsQuasisimple (K ⧸ pCore 2 K) ∧
            ⁅R, centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) ∧
            PairProductAction R I D.sourceOrbit U ∧
            NaturalSectionAction R (D.sourceOrbit ⊓ I.pCoreIn 2) U ∧
            PairNaturalAction R I D.sourceOrbit U i ∧
            PairMultiplicityAction R I D.sourceOrbit U i ∧
            (Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
             Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) ∧
            ((PairCubicTensor R I D.sourceOrbit U ∧ primeRank 3 K ≤ 1) ∨
              (PairQuinticTensor R I D.sourceOrbit U ∧ QuinticComponentAction R K I U ∧
                R = K ∧ (R.subgroupOf (normalizer (U : Set G))).Normal)) := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,hK⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_source_tensor
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hn,hpair,hm,hsieve,htensor⟩ := hK
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,_,_,_,_,hIC,_⟩ := selected_one_fixed_subgroup s D.sourceOrbit_weakClosure_setup
    1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  let := hq
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKU).toMonoidHom) (subgroupOfEquivOfLe hKU).surjective
  have hnontriv : ¬ R ≤ centralizer (U : Set G) := by
    intro hc
    have he : R = R.pCoreIn 2 := (inf_eq_left.mpr hc).symm.trans hker
    have ht : pCore 2 R = ⊤ := by
      apply map_injective R.subtype_injective
      simpa only [pCoreIn, ← MonoidHom.range_eq_map, range_subtype] using he.symm
    obtain ⟨e⟩ := hR
    have hcq : Nat.card (R ⧸ pCore 2 R) = 1 := by rw [ht]; simp
    have hcs : Nat.card SL(2,E 1) = 60 := by
      rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,card_E]
      norm_num
    have hec := Nat.card_congr e.toEquiv
    change Nat.card (R ⧸ pCore 2 R) = _ at hec
    omega
  have hKI : ⁅K,I⁆ ≤ K.pCoreIn 2 :=
    Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.containingComponent_commutator
      L K U I hRK hKU hNK hnontriv hIC
  have hVI : D.sourceOrbit ≤ I := s.generate ▸ le_sup_left
  have hUP : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) (inf_le_left.trans hVI)
    (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U := by
    exact (selected_one_core_residual_product s).trans
      (congrArg (fun Z => ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ Z) hUeq.symm)
  have hout : (PairCubicTensor R I D.sourceOrbit U ∧ primeRank 3 K ≤ 1) ∨
      (PairQuinticTensor R I D.sourceOrbit U ∧ QuinticComponentAction R K I U ∧
                R = K ∧ (R.subgroupOf (normalizer (U : Set G))).Normal) := by
    rcases htensor with hc | ht
    · have hUne : U ≠ ⊥ := by
        intro hb
        have hr : rank U = 4 := hu
        rw [hb,Representation.BinaryOffender.rank_bot] at hr
        omega
      have hSQTK : IsSQTK KnownSimple.IsKnownSimple (normalizer (U : Set G)) :=
        h.simpleQTKE.twoLocal_sqtk ⟨U,hUne,IsElementaryAbelian.isPGroup 2 U,rfl⟩
      have hc' := hc
      obtain ⟨_,_,_,_,_,_,eI,_⟩ := hc'
      exact Or.inl ⟨hc,FourSpaceInspection.containingComponent_threeRank_le_one
        KnownSimple.IsKnownSimple L K U I hSQTK hRK hKU hNK hnontriv hIC eI⟩
    · have hact := quintic_component_action hp ht hRK hKU
        (le_sup_right.trans hRI) hKI hUP hfull hIC
      have hcardU : Nat.card U = 16 := by
        obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
        have hr : rank U = d := by rw [rank,hd,Nat.log_pow Nat.one_lt_two]
        have hd4 : d = 4 := hr.symm.trans hu
        rw [hd,hd4]
        norm_num
      have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
        (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
          ((hTU.trans hNK).trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
      have hQR : K.pCoreIn 2 ≤ normalizer (R : Set G) := hQT.trans
        (Chapter8.Section02.Normalizer.normalizes_localResidual L U T
          D.sylow_normalizes_component hTU)
      have heq := quintic_component_eq hact hcardU hR.some hnontriv hQR
      have hnormal : (R.subgroupOf (normalizer (U : Set G))).Normal := by
        rw [show R = K from heq]
        exact normal_subgroupOf_of_le_normalizer hNK
      exact Or.inr ⟨ht,hact,heq,hnormal⟩
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,
    K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hn,hpair,hm,hsieve,hout⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
