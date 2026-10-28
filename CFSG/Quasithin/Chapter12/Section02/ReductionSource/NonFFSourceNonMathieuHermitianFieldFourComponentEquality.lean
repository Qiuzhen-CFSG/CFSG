module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourComponentAction
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCubicAction
/-!
# The same original Hermitian residual fills its containing component

The cubic branch now uses the completed finite overgroup inspection on the
actual Hermitian four-space U, transported through its deleted-permutation
A₅ marking. The previously constructed commuting section gives m₃(K) ≤ 1.
The original T normalizes the two-core and the residual; quasisimplicity
lifts equality of their action images through the full central kernel.
Together with the retained quintic F₁₆ argument this proves R=K and relative
normality in N_G(U) for both selected tensor alternatives on the same U.

The same H-star group acts on R, and its two-residual centralizes U
and commutes with R modulo O₂(R), the opening step of 8.2.9.
All additional inputs are discharged from the literal chosen module.
Positive weak closure remains explicit; the zero branch and 8.2.9–13
remain with the original non-FF contradiction.
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

/-- Both original selected tensor alternatives give R=K and normality in N_G(U),
with no inspection, action comparison or component equality premise. -/
theorem sourceOrbit_hermitian_tensor_selected_component_eq
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
              (PairQuinticTensor R I D.sourceOrbit U ∧ QuinticComponentAction R K I U)) ∧
            R = K ∧ (R.subgroupOf (normalizer (U : Set G))).Normal ∧
            H ≤ normalizer (R : Set G) ∧
            (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
            ⁅R,(pResidual 2 H).map H.subtype⁆ ≤ R.pCoreIn 2 := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,K,hKU,hK,hRK,hNK,hq,hcomm,
    hRI,hRP,hp,hnat,hpair,hm,hsieve,ht⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_component_action
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
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
    have htop : pCore 2 R = ⊤ := by
      apply map_injective R.subtype_injective
      simpa only [pCoreIn, ← MonoidHom.range_eq_map, range_subtype] using he.symm
    obtain ⟨e⟩ := hR
    have hcq : Nat.card (R ⧸ pCore 2 R) = 1 := by rw [htop]; simp
    have hcs : Nat.card SL(2,E 1) = 60 := by
      rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,card_E]
      norm_num
    have hec := Nat.card_congr e.toEquiv
    change Nat.card (R ⧸ pCore 2 R) = _ at hec
    omega
  have hout : ((PairCubicTensor R I D.sourceOrbit U ∧ primeRank 3 K ≤ 1) ∨
      (PairQuinticTensor R I D.sourceOrbit U ∧ QuinticComponentAction R K I U)) ∧ R = K := by
    rcases ht with ⟨hc,hrank⟩ | ⟨hq,hact,heq,_⟩
    · obtain ⟨b,f,_,hrange,he⟩ :=
        D.sourceOrbit_hermitian_selected_fixed_sl2_action h.toHypothesis1221 d s
      exact ⟨Or.inl ⟨hc,hrank⟩,cubic_component_eq L K U T hRK hKU hNK
        D.sylow_normalizes_component hTU hnontriv hrank b f hrange he⟩
    · exact ⟨Or.inr ⟨hq,hact⟩,heq⟩
  have hnormal : (R.subgroupOf (normalizer (U : Set G))).Normal := by
    rw [hout.2]
    exact normal_subgroupOf_of_le_normalizer hNK
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨hHN,hres⟩ := selected_one_hstar_normalizer s hH
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  have hHR : H ≤ normalizer (R : Set G) := by
    rw [hout.2]
    exact hHN.trans hNK
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,
    K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hnat,hpair,hm,hsieve,hout.1,hout.2,hnormal,hHR,hres,
    (commutator_mono le_rfl hres).trans hcomm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
