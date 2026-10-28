module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Signalizer
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.OrdinaryConclusion
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NormalizerThetaSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The original local residual escapes the plus kernel

The genuine point-residual generation V₃=[V₃,L₁] and the earlier
noncentrality of V₃ on O₂(G₁) show L₁ is not contained in C_H(UH/U0).
If a nontrivial normal two-perfect subgroup K of this kernel lay in M,
the original TI and theta theorems would put it in the scope of13.3.9.
That theorem gives K=L₁, contradicting the preceding exclusion.

The full earlier structural12.2.2 implication and13.5.4(5) are retained
as genuine source inputs. Neither kernel faithfulness nor K outside M
is assumed. Source:13.7.4(1), first and third paragraphs, pp.936--937.
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_local_residual_eq
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ = sourceOne L T V₁ := by
  have hh := normalizer_residual_eq L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
  change sourceOne L T V₁ =
    (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      (L ⊓ normalizer (V₁ : Set G)).subtype at hh
  have hn : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) := h.normalizer_point_eq
  rw [hn] at hh
  exact hh.symm

/-- L₁ is excluded from the actual plus kernel by full seed generation. -/
theorem local_residual_not_le_kernel
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤
      kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hgen : ⁅V₃, F.L₁⁆ = V₃ := by
    rw [source_local_residual_eq d h]
    exact ModelExclusions.seed_commutator_point_residual d
  intro hc
  have h3 : V₃ ≤ fixedLayer F := hgen.symm.le.trans
    ((commutator_mono (le_conjugateSpanBy V₃ H) hc).trans (kernel_commutator (D := F)))
  have h3point : V₃ ≤ V₁ :=
    (le_inf le_rfl (h3.trans inf_le_right)).trans_eq
      (seed_centralizer_eq_line d h (seed_noncentral_on_local_core h hHG hne))
  exact (not_le_of_gt h.point_lt) h3point

/-- The source K outside M conclusion, with13.3.9 applied to that exact K.
Only genuine earlier global/structural hypotheses and noncentrality remain. -/
theorem normal_kernel_not_le_local
    (h1223 : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Chapter12.Section02.Structural1222.{u} KnownSimple.IsKnownSimple)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 K) (hKne : K ≠ ⊥) :
    ¬ K ≤ M := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hKH : K ≤ H := hKC.trans (kernel_le_H (D := F))
  have hA := fun (X : Type u) (_ : Group X) (_ : Finite X) =>
    ChapterA.Section02.theoremA_knownSimple (G := X)
  have hC := fun (X : Type u) (_ : Group X) (_ : Finite X) =>
    ChapterA.Section02.theoremC_knownSimple (G := X)
  have htheta := d.source_theta_normalizer h1223.toHypothesis1221 hA hC
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hintersection := d.source_line_intersection h1223 structural hA hC hHG
  intro hKM
  have hKV : K ≤ normalizer (V : Set G) :=
    ((le_inf hKH hKM).trans hintersection.le).trans inf_le_right
  let : IsElementaryAbelian 2 F.V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  have hLP : L ≤ M ⊓ normalizer (V : Set G) := by
    refine le_inf ?_ (le_sup_left.trans d.normalizes_V)
    rw [d.local_normalizer]
    exact L.le_normalizer
  have hPL : M ⊓ normalizer (V : Set G) ≤ normalizer (L : Set G) := by
    rw [d.local_normalizer]
    exact inf_le_left
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α :=
    d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨eL⟩ := nonabelian_source_ordinary d h hU hV
  have he := Section03.PointResidualImage.ordinary_residual_of_f9_theta F h M K
    hLP hPL α hα eL (NaturalAction.linearCoordinate d)
    (fun l v => d.conjugation l v.toMul) htheta hp (le_inf hKM hKV) hKH hKn
  rcases he with hb | hL
  · exact hKne hb
  · exact local_residual_not_le_kernel d h hne (hL ▸ hKC)

end CFSG.Quasithin.Chapter13.Section07.PlusAction
