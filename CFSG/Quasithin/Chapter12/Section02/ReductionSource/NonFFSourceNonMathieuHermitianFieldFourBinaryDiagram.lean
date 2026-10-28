module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourChiefMultiplicity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourSieve
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourTransvectionExclusion
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Only the binary diagram row survives the Hermitian chief action

The same original RH-chief section gives the F₄ multiplicity action of
A = O²(H)V, with kernel exactly O₂(A), and its literal inclusion gives an
injection A/O₂(A) → H/O₂(H) containing the entire two-residual K.
The original V-involution remains a transvection in this faithful quotient.
The minimal-parabolic marker theorem puts it in K in the PSL₂(31) row;
its inverted torus of order fifteen then contradicts the transvection-pair
calculation. Every action and quotient premise is discharged here.

The conclusion retains K, its full center and residual identity, the
original maximal overlap, original T-image and actual DiagramModel witness.
The surviving PSL₃(2) diagram-action obstruction, zero weak closure and
8.2.10–13 are still needed for the final Hermitian contradiction.

Source: Aschbacher–Smith 8.2.9, printed pp.720–721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original nonsolvable H-star quotient has the binary PSL₃(2) residual
and its actual Sylow-induced diagram marking; PSL₂(31) is excluded. -/
theorem sourceOrbit_hermitian_tensor_nonsolvable_binary_diagram
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
    IsEGenerated 1 H ∧ generationParameter H = 1 ∧
    ((normalizer (L : Set G)).subgroupOf H).normalCore = pCore 2 H ∧
    let q := QuotientGroup.mk' (pCore 2 H)
    let M := ((normalizer (L : Set G)).subgroupOf H).map q
    let Tplus := ((T : Subgroup G).subgroupOf H).map q
    ∃ K : Subgroup (H ⧸ pCore 2 H), IsComponent (H ⧸ pCore 2 H) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (H ⧸ pCore 2 H) = K ∧
      center K = ⊥ ∧ K ⊔ Tplus = ⊤ ∧ SingleClauses M K Tplus ∧
      ClassicalGroup.IsPSL K 3 2 ∧ DiagramModel M K Tplus 1 := by
  obtain ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,hmodels⟩ :=
    D.sourceOrbit_hermitian_tensor_nonsolvable_residual_models
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
  refine ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,?_⟩
  rcases hmodels with ⟨h31,_⟩ | h2
  · exfalso
    let := hKN
    obtain ⟨hn,hB,hw1,I,i,SI,s,hu,hTU,hR,hHR,hp,hnat,hpair,hm,hsieve,hPcore,hYQ,hdisp,
      A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hkill',hRkill,himages,hmove,hHker,hBN,hBZ,hRker,
      v,hv,hvout,hv2,hvact,hmov,hrank,hdim,m,hm2,eR,e,he,hd,
      hAH,hAJ,hAN,μ,hμ,hμker,hμcore,j,hj,hje,hresj,hμmove,a,hav,ha,hr⟩ :=
      D.sourceOrbit_hermitian_tensor_nonsolvable_chief_transvection
        h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
    obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
      hs B C n hdegree hfield hmodel
    have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
      refine ⟨B,C,⟨eQ⟩,?_⟩
      dsimp only
      rw [hdegree]
      exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
    obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
    have hVH := h28.le_sylow.trans h28.le_ambient
    let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
    obtain ⟨S,hS,hP,hM⟩ := h28.minimal
    obtain ⟨hVS,_,_,_⟩ := intrinsic_source_data h28 S hS hP hM
    let q := QuotientGroup.mk' (pCore 2 H)
    let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
    let W := (D.sourceOrbit.subgroupOf H).map q
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
    have hkerS : q.ker ≤ (S : Subgroup H) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal S
    have hPq := ChapterB.minimalParabolic_surjective S hP q
      (QuotientGroup.mk'_surjective _) hkerS
    have hmax : ChapterB.minimalParabolicMax Sq hPq =
        (ChapterB.minimalParabolicMax S hP).map q :=
      (ChapterB.minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective _)
        (by simpa only [q,QuotientGroup.ker_mk'] using ChapterB.minimalParabolicTwoCore_le_core S hP)).symm
    have hMW : ChapterB.minimalParabolicMax S hP ≤
        normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
      rw [←hM,←subgroupOf_normalizer_eq hVH]
      intro x hx
      exact D.sourceOrbit_hstar_intersection_normalizes h hmany hV hnon hH ⟨x.property,hx⟩
    have hMqW : ChapterB.minimalParabolicMax Sq hPq ≤ normalizer (W : Set _) := by
      rw [hmax]
      exact (map_mono hMW).trans (le_normalizer_map q)
    have hKq : K ⊔ (Sq : Subgroup (H ⧸ pCore 2 H))=⊤ := by
      change K ⊔ (S : Subgroup H).map q=⊤
      rw [hS]
      exact hKT
    let A := (pResidual 2 H).map H.subtype ⊔ D.sourceOrbit
    let eqv := LinearMap.GeneralLinearGroup.generalLinearEquiv (E 1) (Fin m → E 1)
    let f : A →* ((Fin m → E 1) ≃ₗ[E 1] (Fin m → E 1)) :=
      eqv.toMonoidHom.comp μ.asGroupHom
    have hfker : f.ker = pCore 2 A :=
      (MonoidHom.ker_comp_of_injective μ.asGroupHom eqv.toMonoidHom eqv.injective).trans hμcore
    let muQ : (A ⧸ pCore 2 A) →* ((Fin m → E 1) ≃ₗ[E 1] (Fin m → E 1)) :=
      QuotientGroup.lift (pCore 2 A) f hfker.ge
    have hmuQ : Function.Injective muQ := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_lift,hfker]
      exact QuotientGroup.map_mk'_self _
    let aq := QuotientGroup.mk' (pCore 2 A) a
    have haj : j aq=q v := by
      rw [hje]
      apply congrArg q
      exact Subtype.ext hav
    have haW : j aq ∈ W := by
      rw [haj]
      exact mem_map_of_mem q hv
    have hane : j aq ≠ 1 := by
      rw [haj]
      exact fun hh => hvout ((QuotientGroup.eq_one_iff (v : H)).mp hh)
    have hmuQrank : Module.finrank (E 1) (LinearMap.range ((muQ aq).toLinearMap-1)) ≤ 1 := hr.le
    exact corefree_parabolic_no_thirty_one_transvection Sq hPq K hKq
      (pCore_quotient_pCore_eq_bot 2) W (map_mono hVS) hMqW
      (by rw [card_E]; norm_num) j hj (hres ▸ hresj)
      muQ hmuQ aq haW hane hmuQrank h31
  · exact h2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
