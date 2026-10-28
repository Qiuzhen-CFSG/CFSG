module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourChiefMultiplicity
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourDiagramActor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourSolvable
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourBinaryExclusion
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Solvability of the original Hermitian H-star overgroup

The remaining nonsolvable binary residual carries the marked transvection
from the original RH-chief section. Its separate diagram witness lifts to
an element of the original T. The natural SL₂(4) coordinates give this
actor a semilinear coefficient operator on the same multiplicity space;
its field automorphism is retained. Through the literal injective quotient
embedding, that operator implements a noninner automorphism of the full
PSL₃(2) residual. The field-four transvection obstruction excludes it.

Thus the original H-star overgroup is solvable. The proved solvable branch
then gives O²(I)=O²(H), H=IT and T-normalization of VA for the original
selected pair. No solvability, outer-action, quotient-embedding or
normalization premise remains beyond the original positive weak-closure
and half-field tensor hypotheses.

Source: Aschbacher–Smith 8.2.9(1–2), printed pp.720–721,
refs/quasithin.pdf. Zero weak closure and 8.2.10–13 remain separate parts
of the full Hermitian exclusion.
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

/-- On positive weak closure the original H-star overgroup is solvable.
Both nonsolvable residual rows are excluded on the actual chief action. -/
theorem sourceOrbit_hermitian_tensor_hstar_solvable
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
    : Group.IsSolvable H := by
  by_contra hsol
  obtain ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,h2,hdiagram,
    t,ht,α,hα,hαx⟩ :=
    D.sourceOrbit_hermitian_tensor_nonsolvable_diagram_actor
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
  let := hKN
  obtain ⟨hn,hB,hw1,I,i,SI,s,hu,hTU,hR,hHR,hp,hnat,hpair,hm,hsieve,hPcore,hYQ,hdisp,
    A₀,B₀,hUA,hAB,hBcore,hel,hirr,hkill,hkill',hRkill,himages,hmove,hHker,hBN,hBZ,hRker,
    v,hv,hvout,hv2,hvact,hmov,hrank,hdim,m,hm2,eR,e,he,hd,
    hAH,hAJ,hAN,μ,hμ,hμker,hμcore,j,hj,hje,hresj,hμmove,a,hav,ha,hr⟩ :=
    D.sourceOrbit_hermitian_tensor_nonsolvable_chief_transvection
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let J := R ⊔ H
  let A := (pResidual 2 H).map H.subtype ⊔ D.sourceOrbit
  let := hel
  let ρ : Representation (ZMod 2) J
      (Additive (NoncentralChiefRefinement.Section A₀ B₀)) :=
    NoncentralChiefRefinement.binarySectionRepresentation A₀ B₀
  have hHA : H ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAH).mp hAN
  obtain ⟨τ,s₀,f,hs₀,hsemis,hpure,hsemif,hf⟩ :=
    natural_coordinates_normalizer (ρ := ρ) le_sup_left hAJ le_sup_right hHR hHA
      m eR e he μ hμ t
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
  have hMW : ChapterB.minimalParabolicMax S hP ≤ normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
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
  have hMqcore : (ChapterB.minimalParabolicMax Sq hPq).normalCore=⊥ := by
    rw [hmax,←hM]
    exact image_normalCore_eq_bot _ _ hcore
  have hWK := corefree_binary_marker_le_component Sq hPq K hKq hMqcore W
    (map_mono hVS) ((ChapterB.minimalParabolicMax_spec Sq hPq).2.trans hMqW) h2
  have hμN : pCore 2 A ≤ μ.ker := by
    intro b hb
    have hh : μ.asGroupHom b=1 := by
      change b ∈ μ.asGroupHom.ker
      rwa [hμcore]
    exact congrArg Units.val hh
  let μq := μ.quotientOfLEKer (pCore 2 A) hμN
  let aq := QuotientGroup.mk' (pCore 2 A) a
  have haj : j aq=q v := by
    rw [hje]
    apply congrArg q
    exact Subtype.ext hav
  have haW : j aq ∈ W := by
    rw [haj]
    exact mem_map_of_mem q hv
  have hane : j aq≠1 := by
    rw [haj]
    exact fun hh => hvout ((QuotientGroup.eq_one_iff (v : H)).mp hh)
  have ha2 : a^2=1 := by
    apply Subtype.ext
    change (a : G)^2=1
    rw [hav]
    exact congrArg (fun x : H => (x : G)) hv2
  let γ := pCoreNormalizerAction 2 A (inclusion hHA t)
  have hγ (b : A ⧸ pCore 2 A) : j (γ b)=q t*j b*(q t)⁻¹ := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) b
    change j (pCoreNormalizerAction 2 A (inclusion hHA t) (QuotientGroup.mk' (pCore 2 A) b)) = _
    rw [pCoreNormalizerAction_mk,hje,hje,←map_inv,←map_mul,←map_mul]
    apply congrArg q
    apply Subtype.ext
    rfl
  have hfq (b : A ⧸ pCore 2 A) (z : Fin m → E 1) :
      f (μq b z)=μq (γ b) (f z) := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) b
    change f (μ b z)=μq (pCoreNormalizerAction 2 A (inclusion hHA t)
      (QuotientGroup.mk' (pCore 2 A) b)) (f z)
    rw [pCoreNormalizerAction_mk]
    exact hf b z
  exact embedded_binary_residual_transvection_false K h2
    (by rw [card_E]; norm_num) j hj (hres ▸ hresj) μq aq (hWK haW)
    (by rw [←map_pow,ha2,map_one]) hane hr (q t) α hα hαx γ hγ f hfq

/-- Source 8.2.9(1–2) on positive weak closure, with solvability now proved
and the original selected pair and Sylow group retained. -/
theorem sourceOrbit_hermitian_tensor_parabolic
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
    :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∨
          Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 5) ∧
        (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
        (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
        (H : Set G) = (I : Set G) * (T : Set G) ∧
        (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
          (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G) := by
  exact D.sourceOrbit_hermitian_tensor_solvable_parabolic h hmany hV hs hnon B C eQ n
    hdegree hfield hmodel hw hH
    (D.sourceOrbit_hermitian_tensor_hstar_solvable h hmany hV hs hnon B C eQ n
      hdegree hfield hmodel hw hH)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
