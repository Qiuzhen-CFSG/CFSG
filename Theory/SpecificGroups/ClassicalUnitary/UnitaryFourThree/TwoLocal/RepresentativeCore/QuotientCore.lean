module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.CubicDetection

/-!
# Trivial two-core of the quaternion quotient

Assume the concrete quaternion image is normal inside the standard
involution centralizer of PSU₄(3). Two explicit cubic elements detect every
normal two-subgroup of the quotient: its commutators with them have exponent
dividing three, hence are trivial. The common centralizer also has exponent
dividing three, so the two-subgroup itself is trivial.

All matrix facts retain the determinant-compatible GU₂ blocks, their
interchange, and the full scalar kernel of SU₄ → PSU₄. Normality is the only
additional premise; the parent representative-core calculation supplies it.
This is the quotient calculation used for Aschbacher–Smith, condition E and
Theorem 0.1.2(4), printed pp.3–4 of `refs/quasithin.pdf`. The concrete unitary
conventions are those of GLS3, chapter 2, §2.7.
-/

open scoped commutatorElement
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
open QuotientCore.CubicDetection

private theorem cubic_detection {G : Type*} [Group G] (a b : G)
    (ha : ∀ g : G, ⁅g,a⁆ ^ 3 = 1)
    (hb : ∀ g : G, ⁅g,b⁆ ^ 3 = 1)
    (hc : ∀ g : G, ⁅g,a⁆ = 1 → ⁅g,b⁆ = 1 → g ^ 3 = 1) : pCore 2 G = ⊥ := by
  have kill (g : G) (hg : g ∈ pCore 2 G) (h3 : g ^ 3 = 1) : g = 1 := by
    obtain ⟨k,hk⟩ := pCore_isPGroup (p := 2) (G := G) ⟨g,hg⟩
    have h2 : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact (pow_eq_one_iff_of_coprime ((show Nat.Coprime 2 3 by decide).pow_left k)).mp ⟨h2,h3⟩
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply kill g hg
  apply hc g
  · apply kill _ _ (ha g)
    exact Subgroup.commutator_le_left (pCore 2 G) ⊤
      (Subgroup.commutator_mem_commutator hg (Subgroup.mem_top a))
  · apply kill _ _ (hb g)
    exact Subgroup.commutator_le_left (pCore 2 G) ⊤
      (Subgroup.commutator_mem_commutator hg (Subgroup.mem_top b))

/-- The actual projective centralizer modulo its quaternion image has trivial two-core. -/
public theorem quotient_twoCore_eq_bot [quaternionCore.Normal] :
    pCore 2 (standardCentralizer ⧸ quaternionCore) = ⊥ := by
  let π := QuotientGroup.mk' quaternionCore
  have cube_iff (g : standardCentralizer) : π g ^ 3 = 1 ↔ g ^ 3 ∈ quaternionCore := by
    rw [← map_pow]
    exact QuotientGroup.eq_one_iff (g ^ 3)
  apply cubic_detection (π leftCubic) (π rightCubic)
  · intro g
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective quaternionCore g
    rw [← map_commutatorElement]
    exact (cube_iff _).mpr (left_commutator_cube_mem g)
  · intro g
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective quaternionCore g
    rw [← map_commutatorElement]
    exact (cube_iff _).mpr (right_commutator_cube_mem g)
  · intro g hl hr
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective quaternionCore g
    rw [← map_commutatorElement] at hl hr
    apply (cube_iff _).mpr
    exact cube_mem_of_centralizes_cubics g ((QuotientGroup.eq_one_iff _).mp hl)
      ((QuotientGroup.eq_one_iff _).mp hr)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
