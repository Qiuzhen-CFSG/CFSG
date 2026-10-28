module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Rank

/-!
# Relator generators for perfect central kernels

Lift the generators of a presentation to a perfect central extension. The
lifts generate: their image supplements the central kernel, and perfectness
removes the central supplement. Consequently the kernel is the normal closure
of the relator images. Centrality makes this their ordinary subgroup closure.

For a finite abelian group, transfer onto a Sylow subgroup is surjective:
its restriction is the power map given by the prime-to-p Sylow index.
Thus a generator bound for the full kernel also bounds its Sylow subgroups.

These are the presentation and transfer arguments used in the exceptional
PSL₃(4) multiplier calculation; compare Campbell–Havas–Ramsay–Robertson,
*Nice efficient presentations for all small simple groups and their covers*,
LMS J. Comput. Math. 7 (2004), §5.11, and Aschbacher–Smith I.1.3(6).
-/

public section

open scoped IsMulCommutative

namespace PresentedGroup

variable {α E B : Type*} [Group E] [Group B] [Group.IsPerfect E]

/-- In a perfect central extension, lifts of a complete presentation generate
the extension, and their relator images generate its literal kernel. -/
theorem ker_eq_closure_relator_images
    (rels : Set (FreeGroup α)) (q : E →* B)
    (hcentral : q.ker ≤ Subgroup.center E)
    (e : PresentedGroup rels ≃* B) (a : α → E)
    (ha : ∀ i, q (a i) = e (.of i)) :
    q.ker = Subgroup.closure (FreeGroup.lift a '' rels) := by
  let f := FreeGroup.lift a
  have hcomp : q.comp f = e.toMonoidHom.comp (PresentedGroup.mk rels) := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [f, MonoidHom.comp_apply, FreeGroup.lift_apply_of,
      MulEquiv.coe_toMonoidHom, PresentedGroup.of] using ha i
  have hf : Function.Surjective f :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      q f (hcomp ▸ e.surjective.comp (PresentedGroup.mk_surjective rels)) hcentral
  have hk : (q.comp f).ker = Subgroup.normalClosure rels := by
    rw [hcomp, MonoidHom.ker_comp_of_injective _ _ e.injective]
    ext x
    exact PresentedGroup.mk_eq_one_iff
  have hm : (Subgroup.normalClosure rels).map f = q.ker := by
    rw [← hk, ← MonoidHom.comap_ker, Subgroup.map_comap_eq_self_of_surjective hf]
  have hs : FreeGroup.lift a '' rels ⊆ q.ker := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← hm]
    exact Subgroup.mem_map_of_mem f (Subgroup.subset_normalClosure hr)
  have hc : Subgroup.closure (FreeGroup.lift a '' rels) ≤ Subgroup.center E :=
    ((Subgroup.closure_le _).mpr hs).trans hcentral
  let : (Subgroup.closure (FreeGroup.lift a '' rels)).Normal := ⟨by
    intro x hx g
    rw [Subgroup.mem_center_iff.mp (hc hx) g, mul_inv_cancel_right]
    exact hx⟩
  rw [← hm, Subgroup.map_normalClosure _ _ hf]
  exact le_antisymm (Subgroup.normalClosure_le_normal Subgroup.subset_closure)
    Subgroup.closure_le_normalClosure

end PresentedGroup

namespace Sylow

/-- Transfer bounds the number of generators of a Sylow subgroup of a finite
abelian group by the number of generators of the whole group. -/
theorem rank_le_of_isMulCommutative {G : Type*} [Group G] [Finite G]
    [IsMulCommutative G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Group.rank P ≤ Group.rank G := by
  have hc : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro x _ y _
    exact mul_comm y x
  let t := MonoidHom.transferSylow P hc
  apply Group.rank_le_of_surjective t
  intro x
  obtain ⟨y, hy⟩ := (P.isPGroup'.powEquiv' P.not_dvd_index).surjective x
  refine ⟨y, ?_⟩
  exact (MonoidHom.transferSylow_eq_pow P hc y y.property).trans hy

end Sylow
