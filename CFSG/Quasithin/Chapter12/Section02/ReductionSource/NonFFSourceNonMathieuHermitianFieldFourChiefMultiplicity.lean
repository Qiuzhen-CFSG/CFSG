module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourChiefMovement
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefMultiplicity
public import Theory.Representation.CommutingTwoCoreKernel
public import Theory.GroupTheory.PResidual.SylowJoin

/-!
# The marked transvection on the original Hermitian multiplicity space

On the same selected pair and RH-chief section, the image of O²(H)V
commutes with the local residual. Its homogeneous natural coordinates
therefore construct a scalar multiplicity action over the original F₄.
The fixed-space argument kills its two-core; the original H-kernel bound
gives the reverse containment. This quotient embeds through the literal
inclusion into H/O₂(H), with image containing the whole original two-residual.

The original V-involution moves four binary dimensions, hence exactly one
F₄ multiplicity dimension, and remains an involution. Its residual acts
nontrivially. All new normality, action, core and quotient premises are
proved from the original chosen module; no replacement module is assumed.
The full H-kernel equality, the two residual-model exclusions, zero weak
closure and 8.2.10–13 remain for the final Hermitian contradiction.

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

/-- The same original chief section constructs a scalar action of its actual
two-residual together with V; the selected V-involution is a transvection. -/
theorem sourceOrbit_hermitian_tensor_nonsolvable_chief_transvection
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
                  Module.finrank (ZMod 2) (Additive (Section A B)) = m*4 ∧
                  let A := (pResidual 2 H).map H.subtype ⊔ D.sourceOrbit
                  ∃ hAH : A ≤ H, ∃ hAJ : A ≤ J, (A.subgroupOf H).Normal ∧
                    ∃ μ : Representation (E 1) A (Fin m → E 1),
                      (∀ a c z, e (ρ (inclusion hAJ a) (e.symm (fun j => c j • z))) =
                        fun j => μ a c j • z) ∧
                      μ.asGroupHom.ker = (ρ.asGroupHom.comp (inclusion hAJ)).ker ∧
                      μ.asGroupHom.ker = pCore 2 A ∧
                      ∃ j : (A ⧸ pCore 2 A) →* (H ⧸ pCore 2 H),
                        Function.Injective j ∧
                        (∀ a : A, j (QuotientGroup.mk' (pCore 2 A) a) =
                          QuotientGroup.mk' (pCore 2 H) (inclusion hAH a)) ∧
                        pResidual 2 (H ⧸ pCore 2 H) ≤ j.range ∧
                      ¬ (((pResidual 2 H).map H.subtype).subgroupOf A) ≤ μ.asGroupHom.ker ∧
                      ∃ a : A, (a : G) = (v : G) ∧ μ a * μ a = 1 ∧
                        Module.finrank (E 1) (LinearMap.range (μ a-1)) = 1 := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hR,hHR,hp,hnat,hpair,hm,hsieve,hPcore,hYQ,hdisp,
    A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hkill',hRkill,himages,hmove,hHker,hBN,hBZ,hRker,
    v,hv,hvout,hv2,hvact,hmov,hrank,hdim,m,hm2,eR,e,he,hd⟩ :=
    D.sourceOrbit_hermitian_tensor_nonsolvable_natural_chief
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let J := R ⊔ H
  let A := (pResidual 2 H).map H.subtype ⊔ D.sourceOrbit
  let := hel
  let := hirr
  let chiefAdd : AddCommGroup (Additive (Section A₀ B₀)) := inferInstance
  let chiefModule : Module (ZMod 2) (Additive (Section A₀ B₀)) := inferInstance
  let ρ : Representation (ZMod 2) J (Additive (Section A₀ B₀)) := binarySectionRepresentation A₀ B₀
  have hVI : D.sourceOrbit ≤ I := s.generate ▸ le_sup_left
  have hIJ : I ≤ J := s.family.le_ambient.trans le_sup_right
  have hVJ : D.sourceOrbit ≤ J := hVI.trans hIJ
  have hKJ : (pResidual 2 H).map H.subtype ≤ J := (map_subtype_le _).trans le_sup_right
  have hAJ : A ≤ J := sup_le hKJ hVJ
  have hRC := (D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s).1
  have hIC := (D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s 1 d).2.2.2.2.2.2.2.1
  have hk : (R.pCoreIn 2).subgroupOf J ≤ ρ.ker := by
    intro r hr
    apply LinearMap.ext
    intro w
    exact congrArg Additive.ofMul (MulEquiv.congr_fun (hRkill hr) w.toMul)
  have hCI := section_images_commute_of_fixed_kernel (ρ := ρ) hIJ le_sup_left
    (s.family.le_ambient.trans hHR)
    ((Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right) hIC hRC hk
  let q := ρ.asGroupHom
  let K := (centralizer ((q.comp (inclusion (show R ≤ J from le_sup_left))).range : Set _)).comap q
  have hAK : A.subgroupOf J ≤ K := by
    rw [subgroupOf_sup hKJ hVJ]
    apply sup_le
    · intro a ha
      apply mem_centralizer_iff.mpr
      rintro _ ⟨r,rfl⟩
      obtain ⟨x,hx,heq⟩ := ha
      have hxa : inclusion (show H ≤ J from le_sup_right) x = a := Subtype.ext heq
      rw [←hxa]
      apply Units.ext
      apply LinearMap.ext
      intro w
      exact congrArg Additive.ofMul (MulEquiv.congr_fun (himages r ⟨x,hx⟩).eq w.toMul)
    · intro a ha
      apply mem_centralizer_iff.mpr
      rintro _ ⟨r,rfl⟩
      apply Units.ext
      exact (hCI ⟨a,hVI ha⟩ r).eq.symm
  have hAC (a : A) (r : R) : Commute (ρ (inclusion hAJ a)) (ρ (inclusion le_sup_left r)) := by
    have hh := mem_centralizer_iff.mp (hAK (show inclusion hAJ a ∈ A.subgroupOf J from a.property))
      (q (inclusion (show R ≤ J from le_sup_left) r)) ⟨r,rfl⟩
    exact congrArg Units.val hh.symm
  obtain ⟨μ,hμ,hμker⟩ := natural_coordinates_multiplicity (ρ := ρ) le_sup_left hAJ m eR e he hAC
  have hVH : D.sourceOrbit ≤ H := hVI.trans s.family.le_ambient
  have hAH : A ≤ H := sup_le (map_subtype_le _) hVH
  have hAN : (A.subgroupOf H).Normal := by
    rw [subgroupOf_sup (map_subtype_le _) hVH]
    rw [show ((pResidual 2 H).map H.subtype).subgroupOf H = pResidual 2 H from
      comap_map_eq_self_of_injective H.subtype_injective _]
    apply pResidual_sup_normal_of_sylow_normalizes (T.subtype hH.1.1.2)
    rw [←subgroupOf_normalizer_eq hVH]
    exact fun _ ht => D.sourceOrbit_weakClosure_setup.normalizes ht
  have hHA : H ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAH).mp hAN
  have hHQ : H ≤ normalizer (A.pCoreIn 2 : Set G) := hHA.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hQJ : A.pCoreIn 2 ≤ J := (pCoreIn_le 2 A).trans hAJ
  have hkillA := twoGroup_kernel_of_commuting_supplement ρ
    (R.subgroupOf J) (H.subgroupOf J) ((A.pCoreIn 2).subgroupOf J)
    (by rw [←subgroupOf_sup (show R ≤ J from le_sup_left) (show H ≤ J from le_sup_right)];
        exact subgroupOf_self _)
    (isPGroup_pCoreIn 2 A).comap_subtype
    (by rw [←subgroupOf_normalizer_eq hQJ]; exact fun _ hh => hHQ hh)
    (by intro r a; exact (hAC ⟨a,(pCoreIn_le 2 A) a.property⟩ ⟨r,r.property⟩).symm)
  have hμcore : μ.asGroupHom.ker = pCore 2 A := by
    apply le_antisymm
    · intro a ha
      rw [hμker] at ha
      have hah : (⟨a,hAH a.property⟩ : H) ∈
          ((NoncentralChiefRefinement.sectionAction A₀ B₀).comp (inclusion le_sup_right)).ker := by
        apply MulEquiv.ext
        intro w
        have hh : ρ (inclusion hAJ a) (Additive.ofMul w) = Additive.ofMul w :=
          LinearMap.congr_fun (congrArg Units.val ha) (Additive.ofMul w)
        exact congrArg Additive.toMul hh
      have haq : (a : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype (hHker hah)
      have hap : (a : G) ∈ A.pCoreIn 2 :=
        pCoreIn_inf_le_of_normalizes (hAH.trans H.le_normalizer) ⟨haq,a.property⟩
      exact (mem_map_iff_mem A.subtype_injective).mp hap
    · intro a ha
      rw [hμker]
      apply Units.ext
      exact hkillA (mem_map_of_mem A.subtype ha)
  let fA : A →* (H ⧸ pCore 2 H) :=
    (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)
  have hfA : fA.ker = pCore 2 A := by
    ext a
    change inclusion hAH a ∈ (QuotientGroup.mk' (pCore 2 H)).ker ↔ a ∈ pCore 2 A
    rw [QuotientGroup.ker_mk']
    constructor
    · intro ha
      have hh : (a : G) ∈ A.pCoreIn 2 :=
        pCoreIn_inf_le_of_normalizes (hAH.trans H.le_normalizer)
          ⟨mem_map_of_mem H.subtype ha,a.property⟩
      exact (mem_map_iff_mem A.subtype_injective).mp hh
    · intro ha
      have hh : (a : G) ∈ H.pCoreIn 2 :=
        pCoreIn_mono_of_normalizes hAH hHA (mem_map_of_mem A.subtype ha)
      exact (mem_map_iff_mem H.subtype_injective).mp hh
  let j : (A ⧸ pCore 2 A) →* (H ⧸ pCore 2 H) :=
    QuotientGroup.lift (pCore 2 A) fA hfA.ge
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_lift,hfA]
    exact QuotientGroup.map_mk'_self _
  have hje (a : A) : j (QuotientGroup.mk' (pCore 2 A) a) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hAH a) := rfl
  have hresj : pResidual 2 (H ⧸ pCore 2 H) ≤ j.range := by
    rw [←map_pResidual_of_surjective 2 (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)]
    rintro _ ⟨x,hx,rfl⟩
    let a : A := ⟨x,mem_sup_left (mem_map_of_mem H.subtype hx)⟩
    exact ⟨QuotientGroup.mk' (pCore 2 A) a,rfl⟩
  have hμmove : ¬ (((pResidual 2 H).map H.subtype).subgroupOf A) ≤ μ.asGroupHom.ker := by
    intro hz
    apply hmove
    intro x hx
    let a : A := ⟨x,mem_sup_left hx⟩
    have ha : a ∈ μ.asGroupHom.ker := hz hx
    rw [hμker] at ha
    apply MulEquiv.ext
    intro w
    have hh : ρ (inclusion hAJ a) (Additive.ofMul w) = Additive.ofMul w :=
      LinearMap.congr_fun (congrArg Units.val ha) (Additive.ofMul w)
    exact congrArg Additive.toMul hh
  let a : A := ⟨v,mem_sup_right hv⟩
  have ha2 : a^2=1 := Subtype.ext (congrArg (fun x : H => (x : G)) hv2)
  have harank : Module.finrank (ZMod 2) (LinearMap.range (ρ (inclusion hAJ a)-1))=4 := hrank
  obtain ⟨ha,hr⟩ := natural_multiplicity_transvection (ρ := ρ) hAJ m e μ hμ a ha2 harank
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hR,hHR,hp,hnat,hpair,hm,hsieve,hPcore,hYQ,hdisp,
    A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hkill',hRkill,himages,hmove,hHker,hBN,hBZ,hRker,
    v,hv,hvout,hv2,hvact,hmov,hrank,hdim,m,hm2,eR,e,he,hd,hAH,hAJ,hAN,μ,hμ,hμker,hμcore,j,hj,hje,hresj,hμmove,a,rfl,ha,hr⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
