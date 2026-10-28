module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OddReduction
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableB18
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.PointConsumer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.SourceActions

/-!
# Solvable exclusion of binary transvections

The genuine B.1.8 solvable-factor
alternative force a solvable member of `Hz` to have no nonidentity
transvection on its literal `UH/V₁` action.  The proof keeps the source
normalizer, flag and commutator hypotheses explicit; it does not replace the
local action by a model representation.

Source: Aschbacher--Smith, 13.8.5(1), 13.8.12 and 13.8.13,
printed pp. 949--951.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
open TransvectionRecognition TransvectionRecognition.Solvable
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G:Type*} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (hH:H∈Source.Hz (one L T V₁) T G₁ M)
 (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
 (hN:Nonempty ((L⧸pCore 2 L)≃*Atlas.Codes.HexEvenAutomorphisms)→normalizer (zero L:Set G)≤M)
 (hflag:normalizer (V₁:Set G)⊓normalizer (V₃:Set G)≤M⊓normalizer (V:Set G))
 (hdisp:V₁=⁅V₃,Source.QH H⁆)
 [IsElementaryAbelian 2 (Source.UH H V₃)]
include d hH hF9 hN hflag hdisp

theorem no_transvection
    (hs:Group.IsSolvable H)
    (ρ:Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ:IsConjugation H V₃ V₁ ρ) (t:Source.Hstar H) : ¬IsTransvection ρ t := by
  intro ht
  let := hs
  have hcentralizer:commutatorPreimage H (Source.UH H V₃) V₁≤Source.QH H :=
    (OddReduction.source_kernel hF9).symm.le
  have hrank:=TwoFactors.source_threeRank_le_two d hH
  obtain ⟨b,hcount,hJ⟩:=source_normalClosure_factors
    (fun B _ _ _ σ=>solvable_ff_factors B (Additive (Source.Utilde H V₃ V₁)) σ)
    ρ hρ hcentralizer hrank t ht (inferInstance:Group.IsSolvable (normalClosure ({t}:Set (Source.Hstar H))))
  have hc:b.count=1 := by
    by_contra hne
    have htwo:b.count=2 := by omega
    exact TwoFactors.source_two_factors_impossible T d earlier_marked_models hH ρ hρ t ht b hJ htwo
  have hmodels:=local_flag_alternatives d
  have hfactor:=fun W₁ W₃ (a:LocalAction.NaturalSetup L (T:Subgroup G) V W₁ W₃)=>CoverFactorization.source_factorization a
  rcases OneFactor.source_one_factor_alternatives T G₁ M hH hmodels hfactor
    hrank d.line_card d.seed_card ρ hρ t ht b hJ hc with hcomm | ⟨hres,hcover⟩ | ⟨_,hmoved⟩
  · have hgen:=seed_generation_of_core_displacement d hH hmodels hfactor hdisp
    exact centralizing_one_factor_impossible ρ hρ (one L T V₁) (le_sup_left.trans hH.1.2)
      hgen hcentralizer t ht b hJ hc hcomm
  · exact hH.2.2 (le_M_of_preimageResidual_eq H M (zero L) _ hres (hN hcover))
  · exact hH.2.2 (le_M_of_movedSpace_eq ρ hρ (d.line_le_plane.trans d.plane_le_seed) M
      (d.first_normalizer ▸ hH.2.1) (hflag.trans inf_le_left) _ hmoved)

open SolvableExclusion
open Three.Supercritical.Offenders

theorem no_star_transvection
    (hs:Group.IsSolvable H) (a:Five.StarAction H (Source.UH H V₃) V₁)
    (t:Source.Hstar H) (hne:a.action t≠1) :
    CriticalGeometry.binaryLinear (a.action t)∉LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := by
  rintro ⟨f,v,hfv,he⟩
  have hformula (w:Additive (Source.Utilde H V₃ V₁)) :
      linearAction a t w=w+f w•v := congrArg (fun b=>b w) he
  have hf:f≠0 := by
    intro hz
    apply hne
    ext w
    have hh:=hformula (Additive.ofMul w)
    have hh' : linearAction a t (Additive.ofMul w) = Additive.ofMul w := by
      simpa only [hz,LinearMap.zero_apply,zero_smul,add_zero] using hh
    exact congrArg Additive.toMul hh'
  have hv:v≠0 := by
    intro hz
    apply hne
    ext w
    have hh:=hformula (Additive.ofMul w)
    have hh' : linearAction a t (Additive.ofMul w) = Additive.ofMul w := by
      simpa only [hz,smul_zero,add_zero] using hh
    exact congrArg Additive.toMul hh'
  have hρ:IsConjugation H V₃ V₁ (linearAction a) := fun h u=>a.conjugation h u
  exact no_transvection d hH hF9 hN hflag hdisp hs (linearAction a) hρ t ⟨f,v,hf,hv,hfv,hformula⟩

open CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry

/-- The center action is the same literal star action after the quotient map.
Thus the antecedent of the earlier full-model implication is impossible in a
solvable member of `Hz`. -/
theorem no_center_transvection
    (hs : Group.IsSolvable H)
    (a : Five.StarAction H (Source.UH H V₃) V₁) :
    ¬ (∃ h : H, (centerAction a).action h ≠ 1 ∧
      CriticalGeometry.binaryLinear ((centerAction a).action h) ∈
        LinearEquiv.transvections (ZMod 2)
          (Additive (Source.Utilde H V₃ V₁))) := by
  rintro ⟨h, hh, ht⟩
  have hstar : a.action (QuotientGroup.mk' (pCore 2 H) h) ≠ 1 := by
    simpa [centerAction] using hh
  exact (no_star_transvection d hH hF9 hN hflag hdisp hs a
    (QuotientGroup.mk' (pCore 2 H) h) hstar) ht

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
