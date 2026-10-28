module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourSieve
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefNatural

/-!
# A moved chief section for the original Hermitian H-star group

The selected pair's full two-core is subnormal in RH, hence lies in its
two-core. Its faithful action on P/U makes the actual O²(H) move that
mixed two-core modulo U. Refinement constructs an actual chief section
above U, with both endpoints normal in RH. Its binary irreducibility
kills the mixed two-core and the entire local residual two-core, and the
original commutator bound makes the R and O²(H) images commute. The
original natural B₀/U survives in the section with denominator exactly U,
so the full R-action kernel is exactly O₂(R). An involution in the original
V outside O₂(H) moves this same section.

All section and movement inputs are discharged from the original chosen
module, the same selected pair and the actual half-field tensor marking.
B.6.8(6a) and the completed maximal-core identification also bound the
original H-action kernel by O₂(H) in the nonsolvable branch. The reverse
containment, homogeneous natural restriction and
multiplicity transvection argument are still required for 8.2.9.
Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
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
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The literal chosen-module action supplies a chief section of O₂(RH)/U
moved by its original two-residual, with the original pair and commuting images. -/
theorem sourceOrbit_hermitian_tensor_nonsolvable_moved_chief
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
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsol : ¬Group.IsSolvable H) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        let U := D.sourceOrbit ⊓ centralizer
          (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
        let R := Chapter8.Section02.Normalizer.localResidual L U
        let J := R ⊔ H
        rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
        H ≤ normalizer (R : Set G) ∧
        PairProductAction R I D.sourceOrbit U ∧
        NaturalSectionAction R (D.sourceOrbit ⊓ I.pCoreIn 2) U ∧
        PairNaturalAction R I D.sourceOrbit U i ∧
        PairMultiplicityAction R I D.sourceOrbit U i ∧
        (Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
          Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) ∧
        I.pCoreIn 2 ≤ J.pCoreIn 2 ∧ J.pCoreIn 2 ≤ H.pCoreIn 2 ∧
        ⁅J.pCoreIn 2,D.sourceOrbit⁆ ≤ D.sourceOrbit ⊓ I.pCoreIn 2 ∧
        ∃ A B : NormalNode J, U.subgroupOf J ≤ A.val ∧
          A ⋖ B ∧ B.val ≤ pCore 2 J ∧
          ∃ he : IsElementaryAbelian 2 (Section A B), letI := he
            Representation.IsIrreducible (binarySectionRepresentation A B) ∧
            pCore 2 J ≤ (binarySectionRepresentation A B).ker ∧
            let f := NoncentralChiefRefinement.sectionAction A B
            pCore 2 J ≤ f.ker ∧ (R.pCoreIn 2).subgroupOf J ≤ f.ker ∧
            (∀ (r : R) (a : pResidual 2 H),
              Commute (f (inclusion le_sup_left r)) (f (inclusion le_sup_right a.val))) ∧
            ¬ (((pResidual 2 H).map H.subtype).subgroupOf J) ≤ f.ker ∧
            (f.comp (inclusion le_sup_right)).ker ≤ pCore 2 H ∧
            (D.sourceOrbit ⊓ I.pCoreIn 2) ≤ B.val.map J.subtype ∧
            (D.sourceOrbit ⊓ I.pCoreIn 2) ⊓ A.val.map J.subtype = U ∧
            (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
            ∃ v : H, (v : G) ∈ D.sourceOrbit ∧ v ∉ pCore 2 H ∧ v^2 = 1 ∧
              f (inclusion le_sup_right v) ≠ 1 := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,K,hKU,hK,hRK,hNK,hq,hcomm,
    hRI,hRP,hp,hnat,hpair,hm,hsieve,ht,heq,hnorm,hHR,hres,hRc,h3,h5,
    hcore,hinter,himage,hPQ,hYQ,hdisp,hqdisp,e,he⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_parabolic_core
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
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←selected_generates_hstar s hH]
    exact sup_le (hIC.trans (Subgroup.centralizer_le_normalizer _)) hTU
  obtain ⟨hPcore,A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hmove⟩ := selected_one_moved_chief s
    hH.1.1.2 D.sourceOrbit_weakClosure_setup.normalizes hHR (le_sup_left.trans hRP)
    (hPQ.le.trans inf_le_right) hUP hHU hp hsieve
  obtain ⟨hkill',hRkill,himages⟩ := mixed_chief_actions_commute hHR hRc A₀ B₀ hAB hBcore
  have hmodels := D.sourceOrbit_hermitian_tensor_nonsolvable_residual_models
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  have hHker := hstar_chief_kernel_le le_sup_right h28 hmodels.2.2.1 A₀ B₀ hmove
  have hout : ¬ D.sourceOrbit.subgroupOf H ≤ pCore 2 H := by
    intro hv
    have hz : (D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by simpa only [QuotientGroup.ker_mk'] using hv)
    rw [hz,card_bot] at himage
    omega
  obtain ⟨v,hv,hvout⟩ := SetLike.not_le_iff_exists.mp hout
  have hv2 : v^2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (A := D.sourceOrbit) (v : G) hv)
  have hvact : NoncentralChiefRefinement.sectionAction A₀ B₀ (inclusion le_sup_right v) ≠ 1 := by
    intro hvk
    exact hvout (hHker hvk)
  let J := R ⊔ H
  let N := B₀.val.map J.subtype
  let Z := A₀.val.map J.subtype
  have hJN : J ≤ normalizer (N : Set G) := by
    have hh := B₀.val.le_normalizer_map J.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hJZ : J ≤ normalizer (Z : Set G) := by
    have hh := A₀.val.le_normalizer_map J.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hUZ : U ≤ Z := by
    have hh := map_mono (f := J.subtype) hUA
    rwa [map_subgroupOf_eq_of_le (hUP.trans ((pCoreIn_le 2 I).trans
      (s.family.le_ambient.trans le_sup_right)))] at hh
  have hNQ : N ≤ J.pCoreIn 2 := map_mono hBcore
  have hVJ : D.sourceOrbit ≤ J := hVI.trans (s.family.le_ambient.trans le_sup_right)
  have hnot : ¬ ⁅N,D.sourceOrbit⁆ ≤ Z := by
    intro hc
    apply hvact
    apply MulEquiv.ext
    intro x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (A₀.val.subgroupOf B₀.val) x
    rw [NoncentralChiefRefinement.sectionAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply (mem_map_iff_mem J.subtype_injective).mp
    change (v : G) * (b.val : G) * (v : G)⁻¹ / (b.val : G) ∈ Z
    rw [commutator_comm] at hc
    simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using
      hc (commutator_mem_commutator hv (mem_map_of_mem J.subtype b.property))
  obtain ⟨hBN,hBZ⟩ := hnat.survives_moved_interval (le_inf inf_le_left hUP)
    N Z D.sourceOrbit hUZ (map_mono hAB.le) (le_sup_left.trans hJN)
    (le_sup_left.trans hJZ) (hVJ.trans hJN)
    ((commutator_mono hNQ le_rfl).trans hdisp) hnot
  have hRker : ((NoncentralChiefRefinement.sectionAction A₀ B₀).comp
      (inclusion le_sup_left)).ker = pCore 2 R := by
    ext r
    constructor
    · intro hr
      apply (hnat.kernel r).mp
      intro b
      obtain ⟨x,hx,hxb⟩ := hBN b.property
      let x' : B₀.val := ⟨x,hx⟩
      have hfix : NoncentralChiefRefinement.sectionAction A₀ B₀
          (inclusion le_sup_left r) (QuotientGroup.mk' (A₀.val.subgroupOf B₀.val) x') =
            QuotientGroup.mk' (A₀.val.subgroupOf B₀.val) x' :=
        MulEquiv.congr_fun hr _
      rw [NoncentralChiefRefinement.sectionAction_mk] at hfix
      have hh := QuotientGroup.eq_iff_div_mem.mp hfix
      change (inclusion le_sup_left r * x * (inclusion le_sup_left r)⁻¹) / x ∈ A₀.val at hh
      have hh' := mem_map_of_mem J.subtype hh
      change (r : G) * (x : G) * (r : G)⁻¹ / (x : G) ∈ Z at hh'
      change (x : G) = (b : G) at hxb
      rw [hxb] at hh'
      have hw : ⁅(r : G),(b : G)⁆ ∈ D.sourceOrbit ⊓ I.pCoreIn 2 :=
        (le_normalizer_iff_commutator_le_right.mp hnat.choose)
          (commutator_mem_commutator r.property b.property)
      have hboth : ⁅(r : G),(b : G)⁆ ∈ (D.sourceOrbit ⊓ I.pCoreIn 2) ⊓ Z :=
        ⟨hw,by
          change (r : G) * (b : G) * (r : G)⁻¹ * (b : G)⁻¹ ∈ Z
          simpa only [div_eq_mul_inv] using hh'⟩
      rwa [hBZ] at hboth
    · intro hr
      exact hRkill (mem_map_of_mem R.subtype hr)
  exact ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hR,hHR,hp,hnat,hpair,hm,hsieve,hPcore,hYQ,hdisp,
    A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hkill',hRkill,himages,hmove,hHker,hBN,hBZ,hRker,v,hv,hvout,hv2,hvact⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
