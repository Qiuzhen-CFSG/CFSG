module
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.QuotientLifting
/-!
# Quasisimple images after killing the core commutator

For a perfect group with quasisimple two-core quotient, a homomorphism with
two-group kernel has quasisimple image when it kills [O₂(A),A]. The image is
a perfect central cover of A/O₂(A), through the original quotient maps.

Source: the central-cover step in Aschbacher–Smith C.2.13, p.148.
-/
public section
open Subgroup Theory.GroupTheory
namespace MonoidHom
variable {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
/-- Killing the actual core commutator gives a quasisimple image. -/
theorem quasisimple_range_of_core_commutator_killed (f : A →* B)
    [IsQuasisimple (A ⧸ pCore 2 A)]
    (hk : IsPGroup 2 f.ker) (hc : ⁅pCore 2 A,(⊤ : Subgroup A)⁆ ≤ f.ker) :
    IsQuasisimple f.range := by
  have hker : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hk⟩
  let q := QuotientGroup.mk' f.ker
  let g : (A ⧸ f.ker) →* A ⧸ pCore 2 A :=
    QuotientGroup.lift f.ker (QuotientGroup.mk' (pCore 2 A)) (by
      rw [QuotientGroup.ker_mk']; exact hker)
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective _) _
  have hgc : g.ker ≤ center (A ⧸ f.ker) := by
    rw [QuotientGroup.ker_lift,QuotientGroup.ker_mk']
    rw [← commutator_top_right_eq_bot_iff_le_center,←q.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      MonoidHom.range_eq_map,←map_commutator,Subgroup.map_eq_bot_iff]
    rwa [QuotientGroup.ker_mk']
  let : IsQuasisimple (A ⧸ f.ker) :=
    (show PerfectCentralCovering.Cover (A ⧸ f.ker) (A ⧸ pCore 2 A) from
      { toMonoidHom := g, surjective := hg, isPerfect := inferInstance,
        ker_le_center := hgc }).isQuasisimple
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.quotientKerEquivRange f)
end MonoidHom
