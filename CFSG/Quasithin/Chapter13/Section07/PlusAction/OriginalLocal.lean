module
public import CFSG.Quasithin.Chapter13.Section07.OrdinaryLocalExclusion
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NaturalModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences

/-!
# The selected ordinary plus kernel escapes the original local subgroup

The chosen natural module has trivial L-centralizer, so the earlier FSU
TI theorem applies under the actual Hypothesis12.2.1. A subgroup of the
point centralizer lying in M consequently normalizes V. The ordinary
point-residual theorem then identifies a normal two-perfect such subgroup
with the source residual or the identity. This removes the universal
structural12.2.2 premise from the original plus-kernel escape argument.

Source: Aschbacher--Smith,13.3.9 and13.7.4(1), printed pp.887,937.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Original ordinary 13.3.9 on a normal two-perfect subgroup of the
literal H. Neither of the conjugate-span conclusions is assumed. -/
theorem ordinary_normal_residual_eq
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {K : Subgroup G} (hKH : K ≤ H) (hKM : K ≤ M)
    (hKn : H ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 K) :
    K = ⊥ ∨ K = (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hA := fun (X : Type u) (_ : Group X) (_ : Finite X) =>
    ChapterA.Section02.theoremA_knownSimple (G := X)
  have hC := fun (X : Type u) (_ : Group X) (_ : Finite X) =>
    ChapterA.Section02.theoremC_knownSimple (G := X)
  have htheta := d.source_theta_normalizer h1221 hA hC
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hc : V ⊓ centralizer (L : Set G) = ⊥ := by
    have hh := congrArg (Subgroup.map V.subtype) (ModelExclusions.NaturalModels.centralizer_bot d)
    change ((centralizer (L : Set G)).subgroupOf V).map V.subtype =
      (⊥ : Subgroup V).map V.subtype at hh
    rwa [subgroupOf_map_subtype, Subgroup.map_bot, inf_comm] at hh
  have hTI := d.chosen.ti_of_centralizer_eq_bot h1221 hA hC hc
  have hpoint : V₁ ≠ ⊥ := by
    intro he
    have hh := d.line_card
    rw [he,card_bot] at hh
    contradiction
  have hKV : K ≤ normalizer (V : Set G) :=
    (le_inf (hKM.trans d.local_normalizer.le)
      (hKH.trans (hHG.trans d.first_normalizer.le))).trans
      (inf_normalizer_le_of_trivial_intersections hTI hpoint
        (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)))
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
  exact Section03.PointResidualImage.ordinary_residual_of_f9_theta F h M K
    hLP hPL α hα eL (NaturalAction.linearCoordinate d)
    (fun l v => d.conjugation l v.toMul) htheta hp (le_inf hKM hKV) hKH hKn

/-- The escape step of 13.7.4 on its full ordinary-A₆ domain, including
abelian V_H. The subgroup is only assumed normal and two-perfect in H. -/
theorem ordinary_normal_kernel_not_le_local
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    {K : Subgroup G}
    (hKC : K ≤ PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 K) (hKne : K ≠ ⊥) :
    ¬ K ≤ M := by
  intro hKM
  rcases ordinary_normal_residual_eq d h1221 h eL
    (hKC.trans PlusAction.kernel_le_H) hKM hKn hp with hb | he
  · exact hKne hb
  · exact PlusAction.local_residual_not_le_kernel d h hne (he ▸ hKC)

/-- A normal C-component of the original H escapes M. Solvability of
the point residual discharges the remaining ordinary 13.3.9 alternative. -/
theorem ordinary_normal_component_not_le_local
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {K : Subgroup G} (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : H ≤ normalizer (K : Set G)) : ¬ K ≤ M := by
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  have hp : IsPPerfect 2 K := by
    intro N hn hq
    let := hn
    have hsub : Subsingleton (K ⧸ N) := by
      by_contra! hnontrivial
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  intro hKM
  have hKL : K ≤ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ := by
    rcases ordinary_normal_residual_eq d h1221 h eL hKH hKM hKn hp with hb | he
    · rw [hb]; exact bot_le
    · exact he.le
  rw [PlusAction.source_local_residual_eq d h] at hKL
  let := ModelExclusions.point_residual_solvable d
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (inclusion_injective hKL)
  exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).injective)

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
