module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCore

/-!
# The original M24 pair core on the chosen orbit

Selection takes place inside the same H-star subgroup that normalizes the
original offender three-space. Its compatible pair generates H together
with T and has quotient PSL2(4). The two-core is the product of the original
elementary intersections, with center precisely the same three-space,
elementary central quotient of order 2^12, full order 2^15, and faithful
quotient action by I/O2(I). All maps and normality assertions are intrinsic
to the displayed I before being embedded into the ambient group.

The final existence theorem constructs the initial Sylow-positioned offender
as well. Native code/cocode markings remain explicit in this cocode theorem;
the already proved three-space normalizer action applies to exactly its U.
Recognition of N_L(U)'s residual as the ambient local component, the tensor
structure in 8.2.8, other Mathieu rows and ambient J4 recognition remain with
qt-d-1222-nonff-mathieu. This module does not assert those later conclusions.
Source: Aschbacher--Smith 8.2.2--5 and the opening of 8.2.8,
printed pp.714--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The compatible pair, its full two-core and section kernel on the
original fixed three-space, with all local source premises discharged. -/
theorem sourceOrbit_m24_fixedPlane_canonical_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ∃ (H I : Subgroup G) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
      H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      generationParameter H = 2 ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S ∧
      I ⊔ (T : Subgroup G) = H ∧ I ≤ centralizer (U : Set G) ∧
      IsWOffenderAt D.sourceOrbit (T : Subgroup G) i.val⁻¹ ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ =
        D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2)) ∧
      I.pCoreIn 2 = (D.sourceOrbit ⊓ I.pCoreIn 2) ⊔
        (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) ∧
      (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U ∧
      (∃ _hU : (U.subgroupOf I).Normal,
        centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I) ∧
      ∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
        IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
        Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^12 ∧
        Nat.card (I.pCoreIn 2) = 2^15 := by
  obtain ⟨H,I,i,S,hH,hHC,hHN,hrH,hn,s,ho,ha,ht,hUZ,hUF,hIC⟩ :=
    D.sourceOrbit_m24_fixedPlane_compatible_pair h hmany hV hq hnon a E hE hg hAT
  obtain ⟨_,_,_,_,_,c,_,_,hu,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_many h hmany hV hq hnon a E hE hg
  obtain ⟨_,_,hrank,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_many h hmany hV hq hnon a E hE ho
  have hcoreRank : rank (inducedAutomizer D.sourceOrbit
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = 6 := by
    rw [←ha]
    exact hrank
  have hUF' := hUF
  rw [ha] at hUF'
  exact ⟨H,I,i,S,hH,hHC,hHN,hrH,hn,s,selected_generates_hstar s hH,hIC,
    ho,ha,ht,hUZ,hUF,MathieuPair.selected_two_quotient s,MathieuPair.selected_two_core_product s,
    MathieuPair.selected_two_core_center s hUZ hUF',
    MathieuPair.selected_two_section_kernel s hUZ,
    MathieuPair.selected_two_core_section s hUZ hIC hu hcoreRank⟩

/-- Construct the original Sylow-positioned offender and its compatible
canonical pair and core, without a supplied offender or selection. -/
theorem sourceOrbit_m24_exists_canonical_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v))
    : ∃ g : G, IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      offenderNormalizer D.sourceOrbit g ≤ T ∧
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ∃ (H I : Subgroup G) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
      H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      generationParameter H = 2 ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S ∧
      I ⊔ (T : Subgroup G) = H ∧ I ≤ centralizer (U : Set G) ∧
      IsWOffenderAt D.sourceOrbit (T : Subgroup G) i.val⁻¹ ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ =
        D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2)) ∧
      I.pCoreIn 2 = (D.sourceOrbit ⊓ I.pCoreIn 2) ⊔
        (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) ∧
      (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U ∧
      (∃ _hU : (U.subgroupOf I).Normal,
        centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I) ∧
      ∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
        IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
        Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^12 ∧
        Nat.card (I.pCoreIn 2) = 2^15 := by
  obtain ⟨g,hg,hAT,_⟩ :=
    D.sourceOrbit_m24_exists_fixedPlane_local_of_many h hmany hV hq hnon a E hE
  exact ⟨g,hg,hAT,D.sourceOrbit_m24_fixedPlane_canonical_core
    h hmany hV hq hnon a E hE hg hAT⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
