module
public import Theory.GroupAction.RankTwoCosetGeometry.QuinticShortPaths
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionActors

/-!
# Two-path four-cycle actors in cubic--quintic geometry

A full Sylow overlap makes the radius-one kernel equal to the embedded
two-core. A nonbacktracking two-path with cubic middle vertex is fixed
pointwise by precisely that kernel. Transporting a local order-four actor
along the last edge therefore supplies a four-cycle at its quintic endpoint.

No ambient or graph finiteness is required. This is the first extension
step in the original quintic path argument, with the path conventions of
Aschbacher--Smith F.3.2--4 and F.7.3, pp.270 and311--312.
-/

public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupTheory
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- A full Sylow overlap identifies the local kernel with the intrinsic two-core. -/
theorem base_kernel_eq_core (i : Bool) (S : Sylow 2 (F i))
    (hS : (S : Subgroup (F i)).map (F i).subtype = F false ⊓ F true) :
    ballKernel F (base F i) 1 = (pCore 2 (F i)).map (F i).subtype := by
  have hcommon : ((F false ⊓ F true).subgroupOf (F i)) = (S : Subgroup (F i)) := by
    apply map_injective (F i).subtype_injective
    rw [map_subgroupOf_eq_of_le (by cases i; exact inf_le_left; exact inf_le_right), hS]
  have hcore : ((F false ⊓ F true).subgroupOf (F i)).normalCore = pCore 2 (F i) := by
    rw [hcommon]
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, S.isPGroup'.to_le (S : Subgroup (F i)).normalCore_le⟩
    · exact normal_le_normalCore.mpr (pCore_isPGroup.le_sylow_of_normal S)
  have hh := congrArg (map (F i).subtype) (base_ballKernel_one F i)
  rw [map_subgroupOf_eq_of_le (show ballKernel F (base F i) 1 ≤ F i by
    simpa only [stabilizer, stabilizer_base] using ballKernel_le_stabilizer F (base F i) 1)] at hh
  rw [hcore] at hh
  exact hh

/-- A base-edge actor gives the same local four-cycle along every two-path. -/
theorem two_path_kernel_actor
    (hthree : ((F true).subgroupOf (F false)).index = 3)
    (hfive : ((F false).subgroupOf (F true)).index = 5)
    (hact : ∃ a ∈ ballKernel F (base F false) 1,
      a^4 ∈ ballKernel F (base F true) 1 ∧ a^2 ∉ ballKernel F (base F true) 1)
    (p : BasedWalk (graph F) 2 (base F true)) (hp : p.Nonbacktracking) :
    ∃ a ∈ pathStabilizer F p,
      a^4 ∈ ballKernel F p.endpoint 1 ∧ a^2 ∉ ballKernel F p.endpoint 1 := by
  obtain ⟨a, ha, ha4, ha2⟩ := hact
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdeg := card_neighbors_of_indices F (fun i => if i then 5 else 3) hi
  rcases p with ⟨⟨b, hab⟩, ⟨⟨c, hbc⟩, pend⟩⟩
  have hb : b.type = false := by
    have hh := hab.1
    change true ≠ b.type at hh
    cases ht : b.type <;> simp_all
  have hc : c.type = true := by
    have hh := hbc.1
    rw [hb] at hh
    cases ht : c.type <;> simp_all
  obtain ⟨g, hg, hg'⟩ := incident_common_translate F hbc.2
  rw [hb] at hg
  rw [hc] at hg'
  refine ⟨g*a*g⁻¹, ?_, ?_, ?_⟩
  · rw [pathStabilizer_two_eq_ballKernel_one F _ hp (by rw [hdeg, hb]; decide)]
    rw [←hg]
    exact (conj_mem_ballKernel_iff F g a (base F false) 1).mpr ha
  · change (g*a*g⁻¹)^4 ∈ ballKernel F c 1
    rw [←hg', ←MulAut.conj_apply, ←map_pow]
    exact (conj_mem_ballKernel_iff F g (a^4) (base F true) 1).mpr ha4
  · change (g*a*g⁻¹)^2 ∉ ballKernel F c 1
    rw [←hg', ←MulAut.conj_apply, ←map_pow]
    exact fun hh => ha2 ((conj_mem_ballKernel_iff F g (a^2) (base F true) 1).mp hh)
end Subgroup.CosetGeometry.RankTwo
