module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Radicals
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Orbit
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Assembly

/-!
# The natural complement on the original flag

Transport the checked centralizer and commutator bounds with the actual
point-stabilizer orbit in L ∩ Hᵍ. The existing ordered frame and the proved
radical images then instantiate the source Sylow/Gaschütz theorem. This gives
D = V₁ᵍ C_D(L) for the literal D = C_{Hᵍ}(Uᵍ), with no complement, Sylow,
radical-image or symmetry premise left explicit.

The marked 14.4.2 action alternative remains the ordinary branch hypothesis.
Orthogonal.TwoCore applies this result to its actual natural orthogonal action
and discharges C_D(L)=1 using the already proved residual-generation argument.

Source: Aschbacher--Smith, 14.4.7, printed p.1009; refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry
open LargerDimension.RankCore.GaschutzComplement
universe u w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original flag supplies every premise of the natural complement
construction, including both radical images and the symmetric centralizers. -/
theorem source_natural_complement (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ))) :
    conjugateCentralizer F.H F.U g = rightConjugate (F.Vi 1) g ⊔
      (conjugateCentralizer F.H F.U g ⊓ centralizer (L : Set G)) := by
  let := chosen.elementary
  let := F.U_normal
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  let a := earlierGeometry d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hpoints := source_point_orbits d earlier hq chosen structural alternatives F hne g hg hgP hgH
  obtain ⟨_,hDU,hDW⟩ := source_centralizer_bounds d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH models
  have hb := RankCore.CentralizerGeometry.symmetric_commutator_bounds F.H F.U (F.Vi 1) L V g
    a.H_eq_normalizer a.normalizes (F.le_seed 1) chosen.normalizes
    (fun x hx => (hpoints x hx).imp_right (fun ⟨t,_,ht,he⟩ => ⟨t,ht,he⟩)) hDU
  have hW : F.U ⊓ centralizer (F.Vi 2 : Set G) ≤ centralizer (conjugateCentralizer F.H F.U g : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDW)
  have hfixed := RankCore.CentralizerGeometry.symmetric_fixed_centralizers F.H F.U (F.Vi 1) (F.Vi 2) L V g
    a.H_eq_normalizer a.normalizes (F.le_seed 2) chosen.normalizes hpoints hDW
  obtain ⟨l,hl,hlP,hIV,m,_,_,hcore,_⟩ := source_natural_frame d earlier hq chosen structural alternatives F hne g hg hgP hgH
  obtain ⟨hU,hUg⟩ := source_radical_images d earlier hq chosen structural alternatives F hne g hg hgP hgH l m
  have hVU : V ≤ rightConjugate F.U g := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (le_conjugateSpanBy V F.H)
    change RankCore.CentralizerGeometry.conjugate V g ≤ rightConjugate F.U g at hh
    rwa [RankCore.CentralizerGeometry.conjugate_eq_self V (chosen.normalizes hg)] at hh
  have hcenter : rightConjugate F.U g ⊓ centralizer (rightConjugate F.U g : Set G) = rightConjugate (F.Vi 1) g := by
    have hc : F.U ⊓ centralizer (F.U : Set G) = F.Vi 1 := (centerIn_eq_inf_centralizer F.U).symm.trans hZ
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hc
    rwa [map_inf _ _ _ (MulAut.conj g⁻¹).injective,RankCore.CentralizerGeometry.centralizer_map] at hh
  exact (source_complement_of_g25 F.H F.U V (F.Vi 1) (F.Vi 2) L g l hg hl
    (source_span_eq d earlier hq chosen structural alternatives F hne g hg hgP hgH) hIV
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) hVU
    (map_mono F.U_le_H) (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2)
    hW (hfixed l hl) (source_seed_fixed_bot d earlier hq chosen structural alternatives F hne g hg hgP hgH)
    hcenter m hU hUg (source_span_kernel d earlier hq chosen structural alternatives F hne g hg hgP hgH)
    (source_span_core_normalizes d earlier hq chosen structural alternatives F hne g hg hgP hgH) hcore).1
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
