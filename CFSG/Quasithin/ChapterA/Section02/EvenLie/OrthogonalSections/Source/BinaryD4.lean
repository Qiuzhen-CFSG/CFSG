module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.BinaryD4Cover
public import Theory.GroupTheory.NonsolvableTwoLocal
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections.Source

/-!
# The binary split rank-four exclusion for odd central covers

The three actual commuting cubic root words lift through every odd central
kernel. They remain independent in the involution centralizer because their
images retain the original marked embedding. Its rank is therefore at least
three, contradicting quasithinness of the original group.

Only oddness of the actual center is needed. The Case II source assembly
supplies it from A.2.13; no quasithinness of a quotient or multiplier
classification is assumed. Source: Aschbacher–Smith A.2.18, printed p.40.
-/
public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The binary D₄ local obstruction survives every odd central cover. -/
theorem false_of_binary_D4_odd_center (hG : IsQuasithin G)
    (ho : Odd (Nat.card (center G)))
    (e : (G ⧸ center G) ≃* ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  obtain ⟨z,hzn,hzs,hr⟩ :=
    ClassicalOrthogonal.A02ParabolicSections.BinaryD4.exists_lifted_local_rank_three
      q hq (by rw [hk]) (by rwa [hk])
  have hz : orderOf z = 2 := orderOf_eq_prime hzs hzn
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG (centralizer ({z} : Set G))
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hz) 3 (by decide) (by decide)
  omega

/-- The endpoint and higher parabolic sections give the full binary plus rank bound. -/
theorem binary_plus_odd_center_quotient_rank_le_three
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (ho : Odd (Nat.card (center G)))
    {r : ℕ} (e : (G ⧸ center G) ≃* ClassicalOrthogonal.POmegaPlus r (ZMod 2)) : r ≤ 3 := by
  have hr := binary_plus_center_quotient_rank_le_four ih hG hK e
  by_contra h
  have he : r = 4 := by omega
  subst r
  exact false_of_binary_D4_odd_center hG ho e

end CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections
