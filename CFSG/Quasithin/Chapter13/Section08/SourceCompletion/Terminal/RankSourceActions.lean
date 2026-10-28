module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.ModuleAction
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy
public import Theory.GroupAction.Quadratic

/-!
# The actual section action in the terminal rank calculation

The original natural flag supplies [V_H,O₂(H)] = U_H. Conjugation therefore
descends to the literal quotient V_H/U_H through H/O₂(H). The endpoint
elementary abelian group acts quadratically, and this property survives the
actual H-conjugator carrying the endpoint to the base edge. Thus the action
and quadraticity hypotheses of 13.8.34 require no additional source input.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.7.3(6), 13.8.4(6), and 13.8.34, printed pp.936,947,968.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
open CriticalGeometry CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open TransvectionRecognition.Component.ModelExtension
open SolvableExclusion.Three.Supercritical.Offenders
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The representation needed in 13.8.34 is constructed on its literal section. -/
theorem exists_rank_section_action
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hHG : H ≤ G₁) (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    [IsElementaryAbelian 2 (Source.VH H V)] :
    ∃ a : SolvableExclusion.Five.StarAction H (Source.VH H V) (Source.UH H V₃),
      SectionConjugation H V V₃ (linearAction a) := by
  have hcore : ⁅Source.VH H V, Source.QH H⁆ ≤ Source.UH H V₃ :=
    (Section07.source_commutator_conclusions (localNaturalSetup d) hF9 hHG hcomm).2.2.2.2.le
  obtain ⟨a⟩ := SolvableExclusion.Five.exists_starAction H (Source.VH H V)
    (Source.UH H V₃) (le_normalizer_conjugateSpanBy V H)
    (le_normalizer_conjugateSpanBy V₃ H) hcore
  exact ⟨a, fun h v => congrArg Additive.ofMul (a.conjugation h v)⟩

/-- Quadraticity is proved for the actual section and actual endpoint actor. -/
theorem rank_section_quadratic
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (a : SolvableExclusion.Five.StarAction H (Source.VH H V) (Source.UH H V₃))
    (c : CriticalPair L (T : Subgroup G) H V) (h : H) :
    IsQuadratic (linearAction a)
      (Source.starImage H (c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom)) := by
  have hg := local_earlierGeometry d hF9 c
  have hq := c.quadratic_star_on_Vsection V₃ hg.Vgamma_H hg.VH_endpoint a.action a.conjugation
  have hfixed := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hq
  have hquad : IsQuadratic (linearAction a) (Source.starImage H c.Vgamma) := by
    intro x hx y hy v
    let ax : (Source.starImage H c.Vgamma).map a.action := ⟨a.action x, mem_map_of_mem _ hx⟩
    let ay : (Source.starImage H c.Vgamma).map a.action := ⟨a.action y, mem_map_of_mem _ hy⟩
    have hm : v.toMul⁻¹ * (ay • v.toMul) ∈
        commutatorAction ((Source.starImage H c.Vgamma).map a.action) (Source.Vsection H V V₃) :=
      subset_closure ⟨ay, v.toMul, mem_top _, rfl⟩
    have hh := hfixed hm
    rw [FixedPoints.mem_subgroup] at hh
    have hh := hh ax
    change a.action x (v.toMul⁻¹ * a.action y v.toMul) =
      v.toMul⁻¹ * a.action y v.toMul at hh
    change a.action x (a.action y v.toMul / v.toMul) = a.action y v.toMul / v.toMul
    simpa only [div_eq_mul_inv, mul_comm] using hh
  rw [MarkedGeometry.starImage_conjugate c.Vgamma hg.Vgamma_H h]
  exact (Representation.OrthogonalFourMinus.RankOne.InnerTransport.quadratic_conj_iff
    (linearAction a) _ _).mpr hquad

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
