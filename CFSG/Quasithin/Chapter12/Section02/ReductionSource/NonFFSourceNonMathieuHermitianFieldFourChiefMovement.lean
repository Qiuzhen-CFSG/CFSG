module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourChief
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefMovement

/-!
# The original Hermitian chief section is homogeneous natural

On the same selected I, original Sylow T and moved RH-chief section, the
full local kernel on U makes the I- and R-actions commute. The actual
involution in V therefore moves exactly the surviving B₀/U, a natural
four-dimensional binary module. Its square-zero displacement gives dimension
at least eight. The equality B₀ = V intersect O₂(H) proves that T preserves
the seed; I commutes with R, so Clifford theory constructs natural copy
coordinates on the whole section with multiplicity at least two.

No homogeneous module, displacement bound or auxiliary action is assumed.
The full H-kernel, multiplicity action exclusions, zero weak closure and the
later 8.2.10–13 arguments remain necessary for the Hermitian contradiction.
Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement Matrix
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

/-- The literal selected chief action has a natural moved four-space and at
least two homogeneous copies over the original four-element field. -/
theorem sourceOrbit_hermitian_tensor_nonsolvable_natural_chief
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
          ∃ hAB : A ⋖ B, B.val ≤ pCore 2 J ∧
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
              f (inclusion le_sup_right v) ≠ 1 ∧
              let ρ : Representation (ZMod 2) J (Additive (Section A B)) := binarySectionRepresentation A B
              let image : Submodule (ZMod 2) (Additive (Section A B)) := (ambientBinarySection J A B hAB.le).imageSpace (D.sourceOrbit ⊓ I.pCoreIn 2)
              let δ : Module.End (ZMod 2) (Additive (Section A B)) := ρ (inclusion le_sup_right v) - 1
              δ.range = image ∧
              Module.finrank (ZMod 2) δ.range = 4 ∧
              8 ≤ Module.finrank (ZMod 2) (Additive (Section A B)) ∧
              ∃ m : ℕ, 2 ≤ m ∧ ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1),
                ∃ e : Additive (Section A B) ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)),
                  (∀ r w, e (ρ (inclusion le_sup_left r) w) =
                    fun j => (eR (QuotientGroup.mk' (pCore 2 R) r)).val *ᵥ (e w j)) ∧
                  Module.finrank (ZMod 2) (Additive (Section A B)) = m*4 := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hR,hHR,hp,hnat,hpair,hm,hsieve,hPcore,hYQ,hdisp,
    A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hkill',hRkill,himages,hmove,hHker,hBN,hBZ,hRker,
    v,hv,hvout,hv2,hvact⟩ :=
    D.sourceOrbit_hermitian_tensor_nonsolvable_moved_chief
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let J := R ⊔ H
  let N := B₀.val.map J.subtype
  let Z := A₀.val.map J.subtype
  let Bnat := D.sourceOrbit ⊓ I.pCoreIn 2
  let := hel
  let chiefAdd : AddCommGroup (Additive (Section A₀ B₀)) := inferInstance
  let chiefModule : Module (ZMod 2) (Additive (Section A₀ B₀)) := inferInstance
  let := hirr
  let ρ : Representation (ZMod 2) J (Additive (Section A₀ B₀)) := binarySectionRepresentation A₀ B₀
  let c := ambientBinarySection J A₀ B₀ hAB.le
  have hRC := (D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s).1
  have hIC := (D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s 1 d).2.2.2.2.2.2.2.1
  have hVI : D.sourceOrbit ≤ I := s.generate ▸ le_sup_left
  have hIJ : I ≤ J := s.family.le_ambient.trans le_sup_right
  have hTJ : (T : Subgroup G) ≤ J := (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hk : (R.pCoreIn 2).subgroupOf J ≤ ρ.ker := by
    intro r hr
    apply LinearMap.ext
    intro w
    exact congrArg Additive.ofMul (MulEquiv.congr_fun (hRkill hr) w.toMul)
  have hCI := section_images_commute_of_fixed_kernel (ρ := ρ) hIJ le_sup_left
    (s.family.le_ambient.trans hHR)
    ((Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right) hIC hRC hk
  let vJ : J := inclusion le_sup_right v
  have hvρ : ρ vJ ≠ 1 := by
    intro hz
    apply hvact
    apply MulEquiv.ext
    intro w
    exact congrArg Additive.toMul (LinearMap.congr_fun hz (Additive.ofMul w))
  have hvC : ∀ r : R, Commute (ρ vJ) (ρ (inclusion le_sup_left r)) := by
    intro r
    exact hCI ⟨v,hVI hv⟩ r
  have hvdisp : ∀ x : N, ⁅(vJ : G),(x : G)⁆ ∈ Bnat := by
    intro x
    have hx : (x : G) ∈ J.pCoreIn 2 := (map_mono hBcore) x.property
    rw [commutator_comm] at hdisp
    exact hdisp (commutator_mem_commutator hv hx)
  obtain ⟨hmov,hrank⟩ := hnat.moved_space (ρ := ρ) c le_sup_left hBN hBZ vJ hvρ hvC hvdisp
  have hdim := hnat.moved_dimension (ρ := ρ) c le_sup_left hBN hBZ vJ
    (congrArg (inclusion (show H ≤ J from le_sup_right)) hv2) hvρ hvC hvdisp
  have hBQ : Bnat ≤ H.pCoreIn 2 := hBN.trans ((map_mono hBcore).trans hYQ)
  have hBeq : Bnat = D.sourceOrbit ⊓ H.pCoreIn 2 := by
    apply le_antisymm (le_inf inf_le_left hBQ)
    exact le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans hVI)).trans
      (pCoreIn_inf_le_of_normalizes (s.family.le_ambient.trans H.le_normalizer)))
  have hTB : (T : Subgroup G) ≤ normalizer (Bnat : Set G) := by
    rw [hBeq]
    exact (le_inf D.sourceOrbit_weakClosure_setup.normalizes
      ((show (T : Subgroup G) ≤ H from hH.1.1.2).trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨m,eR,e,he,hd⟩ := hnat.homogeneous_coordinates (ρ := ρ) c le_sup_left hIJ hTJ
    (sup_le R.le_normalizer hHR)
    (by rw [sup_assoc,selected_generates_hstar s hH]) hBN hBZ hCI hTB
  have hm2 : 2 ≤ m := by omega
  refine ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hR,hHR,hp,hnat,hpair,hm,hsieve,hPcore,hYQ,hdisp,
    A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hkill',hRkill,himages,hmove,hHker,hBN,hBZ,hRker,
    v,hv,hvout,hv2,hvact,?_,hrank,hdim,m,hm2,eR,e,he,hd⟩
  exact hmov

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
