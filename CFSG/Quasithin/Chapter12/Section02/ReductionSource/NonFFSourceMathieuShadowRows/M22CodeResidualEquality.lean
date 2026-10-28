module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeNonsolvableDiagram
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefExclusion
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeParabolicSolvable

/-!
# Residual equality for the original selected M22-code pair

The supplied pair gives the actual cubic quotient, case-I core intersection
and binary residual diagram. The natural homogeneous chief constructed from
its original commutator seed excludes the nonsolvable diagram. The solvable
parabolic argument then identifies the literal two-residuals of I and H,
gives H=IT and makes the original Sylow normalize the original VA.

Every step retains the supplied pair, inverse conjugator and full quotient
kernels. Source: Aschbacher--Smith 8.2.9(1--2), printed pp.720--721,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.MathieuShadowRows MathieuCode.M22Quintet.CocodeTransfer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original M22-code H-star overgroup is solvable. The same selected
pair supplies the actual natural chief and the binary residual diagram;
the resulting field-four transvection and outer actor are incompatible. -/
theorem sourceOrbit_m22_code_selected_hstar_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    Group.IsSolvable H := by
  by_contra hsol
  obtain ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,h2,hdiagram,hVK,
    t,ht,α,hα,hαx⟩ :=
    D.sourceOrbit_m22_code_selected_nonsolvable_diagram_actor h hmany hV hnon d hH s hsol
  obtain ⟨hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,
    f,hfk,hsection,hprod,hpair,hm,hc⟩ :=
    D.sourceOrbit_m22_code_selected_cubic_data h hmany hV hnon d hH s
  obtain ⟨h3,h5⟩ := D.sourceOrbit_m22_code_selected_parabolic_odd_ranks h hmany hV hnon d hH s
  obtain ⟨hcoreI,hinter,himage,_,_⟩ :=
    D.sourceOrbit_m22_code_pair_core_image h hmany hV hnon d hH s h3 h5 hc
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
  let R := localResidual L U
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  have hPH : I.pCoreIn 2 ≤ H.pCoreIn 2 := hcoreI.trans_le inf_le_right
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←selected_generates_hstar s hH]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) hTU
  have hHR : H ≤ normalizer (R : Set G) := by
    rw [←selected_generates_hstar s hH]
    refine sup_le ?_ (normalizes_localResidual L U (T : Subgroup G) D.sylow_normalizes_component hTU)
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono le_rfl hcent).trans hcomm).trans (pCoreIn_le 2 R)
  exact selected_m22_binary_residual_false s hH D.sourceOrbit_weakClosure_setup.normalizes
    hHR hRP hPH hHU hcent hTU hinter hcomm hsection hm hc K h2 hres hVK t α hα hαx

/-- Source 8.2.9(1–2) for the original selected M22-code pair. The literal
residuals are equal, H=IT, and the original VA is normalized by the original T. -/
theorem sourceOrbit_m22_code_selected_residual_equality
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    Group.IsSolvable H ∧ Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∧
      (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (H : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
        offenderNormalizer D.sourceOrbit i.val⁻¹ : Subgroup G) : Set G) := by
  have hsol := D.sourceOrbit_m22_code_selected_hstar_solvable h hmany hV hnon d hH s
  have h28 := (D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH).1
  have h3 := (D.sourceOrbit_m22_code_selected_parabolic_odd_ranks h hmany hV hnon d hH s).1
  have hc := D.sourceOrbit_m22_code_selected_small_quotient h hmany hV hnon d hH s
  obtain ⟨hcard,hres,hTN,hprod,hTVA⟩ := selected_m22_code_solvable_parabolic s h28 hH hsol
    D.sourceOrbit_weakClosure_setup.normalizes h3 hc
  have hA := (D.sourceOrbit_m22_code_selected_cubic_data h hmany hV hnon d hH s).1
  rw [←hA] at hTVA
  exact ⟨hsol,hcard,hres,hTN,hprod,hTVA⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
