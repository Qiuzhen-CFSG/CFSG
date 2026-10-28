module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ModuleGeometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# The weak-closure parameter in the L₃ branch

The original normalizer action is marked through the original L-action.
B.4.8 gives codimension two for every involution in this actual automizer,
so its local minimum is at least two. Control of every ambient hyperplane
centralizer gives r(G,V)>1 directly from the defining infimum, including
the empty-family case. Hence s(G,V)=min(r,m)>1, as required by 12.4.1.

The hyperplane centralizer theorem itself remains an explicit earlier
source input; this module proves the numerical deduction, not 12.4.8.
Source: Aschbacher–Smith, E.3.3–5 and the final proof of 12.4.2, p.816.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
open CFSG.Quasithin.ChapterE
open Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
theorem normalizer_mark (E : SLThreeExtension D)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    (a : Automizer V) : letI := D.elementary
    ∃ b : BinaryLinearThree.Group, automizerRepresentation V a = E.action b := by
  let _ := D.elementary
  obtain ⟨n, hn⟩ := a.property
  obtain ⟨l, hl, he⟩ := hN n n.property
  refine ⟨E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩), ?_⟩
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [E.conjugation]
  change (a.val v.toMul : G) = _
  rw [← hn]
  exact he v.toMul v.toMul.property

/-- B.4.8 bounds the minimum for the full, literal normalizer action. -/
theorem localM_ge_two (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v) : letI := D.elementary
    2 ≤ localM V := by
  let _ := D.elementary
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro n (rfl | ⟨a, ha, rfl⟩)
  · rw [module_finrank_four E hne]
    decide
  · obtain ⟨b, he⟩ := normalizer_mark E hN a
    have hb1 : b ≠ 1 := by
      intro hb
      have ha1 : a = 1 := automizerRepresentation_injective V (by rw [he, hb, map_one, map_one])
      simp [ha1] at ha
    have hb2 : b ^ 2 = 1 := by
      apply action_injective E
      rw [map_pow, ← he, ← map_pow, (orderOf_eq_prime_iff.mp ha).1, map_one, map_one]
    have hb : orderOf b = 2 := orderOf_eq_prime hb2 hb1
    have hc := (involution_linear_plane E hne b hb).2
    have hcodim := fixedCodim_add_finrank E.action (zpowers b)
    rw [module_finrank_four E hne, hc] at hcodim
    have hh : fixedCodim (automizerRepresentation V) (zpowers a) =
        fixedCodim E.action (zpowers b) := by
      rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank, he]
    rw [hh]
    omega

/-- Controlling all actual hyperplanes gives the strict source r-bound. -/
theorem globalR_gt_one_of_hyperplanes
    (V : Subgroup G)
    (hyp : ∀ U ≤ V, subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (V : Set G)) : 1 < globalR V := by
  have htwo : (2 : ℕ∞) ≤ globalR V := by
    apply le_iInf
    intro U
    apply le_iInf
    rintro ⟨hUV, hU⟩
    have hlo : 1 ≤ subgroupCorank V U := by
      have hh := (one_le_globalR V).trans (globalR_le_corank hUV hU)
      exact_mod_cast hh
    have hne : subgroupCorank V U ≠ 1 := fun he => hU (hyp U hUV he)
    have htwo : 2 ≤ subgroupCorank V U := by omega
    exact_mod_cast htwo
  exact lt_of_lt_of_le (by decide) htwo

/-- The exact numerical input to 12.4.1 from the hyperplane bound and B.4.8. -/
theorem globalS_gt_one (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    (hyp : ∀ U ≤ V, subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (V : Set G)) : letI := D.elementary
    1 < globalS V := by
  let _ := D.elementary
  apply lt_min (globalR_gt_one_of_hyperplanes V hyp)
  have hm := localM_ge_two E hne hN
  have hm' : 1 < localM V := by omega
  exact_mod_cast hm'
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
