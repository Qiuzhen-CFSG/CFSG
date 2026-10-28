module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourComponentEquality
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourParabolic

/-!
# The original Hermitian H-star quotient and its pair core

On the same selected U, I, R and K, the natural section now puts
B₀ = V ∩ O₂(I) in O₂(H). The original conjugator puts all of O₂(I)
there, and relative normality gives the exact intersection kernels.
The quotient marking identifies I/O₂(I) with its actual image in H/O₂(H),
while V has image of order two. Residual commutation in the strongly
quasithin N_G(U) bounds both the three- and five-ranks of H by one.
The original mixed two-core displaces V only inside B₀; this also holds
on its literal two-core image in N_G(U)/U.

All new premises are discharged from the original chosen module, tensor
marking and H-star member. Positive weak closure remains explicit. This
supplies the local inputs to 8.2.9; the quotient sieve, chief-section
exclusions, H = IT, zero weak closure and 8.2.10–13 remain with the final
Hermitian contradiction. Source: Aschbacher–Smith, printed pp.720–721,
refs/quasithin.pdf (1 March 2004 manuscript).
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

/-- The literal Hermitian chosen-module application supplies the odd ranks,
full pair-core intersection, quotient marking and mixed-core displacement,
without an extra local action, containment or quotient-comparison premise. -/
theorem sourceOrbit_hermitian_tensor_selected_parabolic_core
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
            ⁅R,(pResidual 2 H).map H.subtype⁆ ≤ R.pCoreIn 2 ∧
            primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 ∧
            R.pCoreIn 2 ⊔ U ≤ H.pCoreIn 2 ∧
            D.sourceOrbit ⊓ I.pCoreIn 2 = D.sourceOrbit ⊓ H.pCoreIn 2 ∧
            Nat.card ((D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 ∧
            I.pCoreIn 2 = I ⊓ H.pCoreIn 2 ∧
            (R ⊔ H).pCoreIn 2 ≤ H.pCoreIn 2 ∧
            ⁅(R ⊔ H).pCoreIn 2,D.sourceOrbit⁆ ≤ D.sourceOrbit ⊓ I.pCoreIn 2 ∧
            ⁅(Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.localImage
                U (R ⊔ H)).pCoreIn 2,
              Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.localImage
                U D.sourceOrbit⁆ ≤
              Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.localImage
                U (D.sourceOrbit ⊓ I.pCoreIn 2) ∧
            ∃ e : (I ⧸ pCore 2 I) ≃*
                ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))),
              ∀ (x : I) (hx : (x : G) ∈ H),
                (e (QuotientGroup.mk' (pCore 2 I) x)).val =
                  QuotientGroup.mk' (pCore 2 H) ⟨x,hx⟩ := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,K,hKU,hK,hRK,hNK,hq,hcomm,
    hRI,hRP,hp,hnat,hpair,hm,hsieve,ht,heq,hnorm,hHR,hres,hRc⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_component_eq
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  have hVI : D.sourceOrbit ≤ I := s.generate ▸ le_sup_left
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro u hu
    have hu' : u ∈ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom := by
      rw [←hUeq]
      exact hu
    obtain ⟨z,hz,rfl⟩ := s.intersection_central hu'
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)
  have hUP : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) (inf_le_left.trans hVI)
    (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hUne : U ≠ ⊥ := by
    intro he
    have hr : rank U = 4 := hu
    rw [he,Representation.BinaryOffender.rank_bot] at hr
    omega
  have hSQTK : IsSQTK KnownSimple.IsKnownSimple (normalizer (U : Set G)) :=
    h.simpleQTKE.twoLocal_sqtk ⟨U,hUne,IsElementaryAbelian.isPGroup 2 U,rfl⟩
  obtain ⟨h3,h5⟩ := selected_one_hstar_odd_ranks s hH D.sylow_normalizes_component
    hIC D.sylow_normalizes_component hTU hcomm hR hSQTK.stronglyQuasithin
  obtain ⟨hcore,hinter,himage⟩ := selected_one_hstar_core_intersection s hH hIC
    D.sylow_normalizes_component hTU (le_inf inf_le_left hUP) hcomm hnat
  have hBQ : D.sourceOrbit ⊓ I.pCoreIn 2 ≤ H.pCoreIn 2 := hinter ▸ inf_le_right
  have hPQ := selected_one_pair_core_in_hstar_core s hBQ
  have hHN : H ≤ normalizer (U : Set G) := by
    rw [←selected_generates_hstar s hH]
    exact sup_le (hIC.trans (Subgroup.centralizer_le_normalizer _)) hTU
  obtain ⟨hYQ,hdisp,hqdisp⟩ := selected_one_hstar_core_displacement s hH
    D.sourceOrbit_weakClosure_setup.normalizes hHN
    ((Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right) hinter
  obtain ⟨e,he⟩ := selected_one_pair_core_quotient s hBQ
  refine ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,K,hKU,hK,hRK,hNK,hq,hcomm,
    hRI,hRP,hp,hnat,hpair,hm,hsieve,ht,heq,hnorm,hHR,hres,hRc,h3,h5,
    hcore,hinter,himage,hPQ,hYQ,hdisp,hqdisp,e,?_⟩
  intro x hx
  exact he x

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
