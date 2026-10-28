module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentSylowNormalizer
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SpanSetup
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.PerfectCover


/-!
# Lifting component Borels to the source intersection

A two-perfect subgroup in a reduced minimal-parabolic image lies in the image
of the two-residual of its maximal subgroup. For the source QRC configuration,
that maximal subgroup is the literal subgroup H ∩ M. Consequently, when its
two-residual centralizes V, each element of a component Sylow normalizer that
is two-perfect has a lift centralizing V.

This is the Borel lifting step in Aschbacher–Smith, `refs/quasithin.pdf`,
proof of 3.1.9(5). The later natural-module argument uses these actual lifts.
-/

public section

open Subgroup Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterB Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

omit [Finite D] in
theorem QrcHypotheses.twoPerfect_image_le_intersection_residual
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (B : Subgroup D) (hB : IsPPerfect 2 B)
    (hBM : B ≤ minimalParabolicMax ((T.subtype h.right_mem.1.1.2).mapSurjective hq)
      (minimalParabolic_reduced_image (T.subtype h.right_mem.1.1.2) hP q hq hc hn).2) :
    B ≤ ((pResidual 2 ((H ⊓ M).subgroupOf H)).map ((H ⊓ M).subgroupOf H).subtype).map q := by
  let S := T.subtype h.right_mem.1.1.2
  have hk := (minimalParabolic_reduced_image S hP q hq hc hn).1
  have hmax : ((H ⊓ M).subgroupOf H).map q =
      minimalParabolicMax (S.mapSurjective hq)
        (minimalParabolic_reduced_image S hP q hq hc hn).2 := by
    rw [←h.intrinsic_maximal_eq_intersection hP]
    exact minimalParabolicMax_map_core S hP q hq hk
  have hm := embedded_pResidual_mono 2 hBM
  rw [(pResidual_eq_top_iff 2 B).mpr hB,←MonoidHom.range_eq_map,range_subtype] at hm
  rw [map_embedded_pResidual,hmax]
  exact hm

theorem QrcHypotheses.twoPerfect_component_image_lifts_fixing_module
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    {L : Subgroup D} (hL : IsComponent D L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L)
    (B : Subgroup D) (hB : IsPPerfect 2 B)
    (hBL : B ≤ L ⊓ normalizer
      ((((T.subtype h.right_mem.1.1.2).mapSurjective hq : Sylow 2 D) : Subgroup D) ⊓ L : Set D)) :
    ∀ b ∈ B, ∃ x : H, q x = b ∧ (x : G) ∈ centralizer (V : Set G) := by
  have hb := h.twoPerfect_image_le_intersection_residual hP q hq hc hn B hB
    (hBL.trans (component_sylow_normalizer_le_maximal
      ((T.subtype h.right_mem.1.1.2).mapSurjective hq)
      (minimalParabolic_reduced_image (T.subtype h.right_mem.1.1.2) hP q hq hc hn).2
      hL heven))
  intro b hbB
  obtain ⟨x,hx,hxb⟩ := hb hbB
  refine ⟨x,hxb,hres ?_⟩
  have hm := mem_map_of_mem H.subtype hx
  rw [map_embedded_pResidual,map_subgroupOf_eq_of_le (show H ⊓ M ≤ H from inf_le_left)] at hm
  exact hm
end CFSG.Quasithin.Chapter3
