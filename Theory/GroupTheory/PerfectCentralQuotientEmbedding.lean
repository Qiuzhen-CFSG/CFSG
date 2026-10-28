module
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Proper nonsolvable subgroups under central quotients

A homomorphism whose kernel lies in the embedded center of a perfect
subgroup preserves every proper inclusion into that subgroup. Otherwise
the smaller subgroup and the center generate the perfect group, contrary
to central nongeneration. Nonsolvability also survives: the restricted
kernel is abelian, so a solvable image would make the original subgroup
solvable.

These facts retain the literal homomorphism and subgroup images. They are
used to pass the special-linear containing component to its projective
quotient in Aschbacher--Smith 5.2.2, printed p.648.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G J : Type*} [Group G] [Group J]

/-- A central kernel preserves proper inclusions into a perfect subgroup. -/
theorem map_lt_of_perfect_of_kernel_le_center
    (f : G →* J) (K R : Subgroup G) [Group.IsPerfect K]
    (hRK : R < K) (hk : f.ker ≤ (center K).map K.subtype) :
    R.map f < K.map f := by
  refine lt_of_le_of_ne (map_mono hRK.le) ?_
  intro he
  have hle : K ≤ R ⊔ f.ker := by
    simpa only [comap_map_eq] using (map_le_iff_le_comap.mp he.ge)
  have hsup : R ⊔ (center K).map K.subtype = K := le_antisymm
    (sup_le hRK.le (map_subtype_le _))
    (hle.trans (sup_le_sup_left hk R))
  have htop : R.subgroupOf K ⊔ center K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRK.le, hsup,
      ← MonoidHom.range_eq_map, range_subtype]
  exact hRK.not_ge (subgroupOf_eq_top.mp (eq_top_of_sup_center_eq_top _ htop))

/-- A central quotient preserves nonsolvability in every subgroup. -/
theorem not_isSolvable_map_of_kernel_le_center
    (f : G →* J) (K R : Subgroup G) (hRK : R ≤ K)
    (hk : f.ker ≤ (center K).map K.subtype) (hR : ¬ Group.IsSolvable R) :
    ¬ Group.IsSolvable (R.map f) := by
  intro hs
  let := hs
  let g := f.subgroupMap R
  have hcentral : g.ker ≤ center R := by
    intro x hx
    have hx' : (x : G) ∈ f.ker := congrArg Subtype.val (show g x = 1 from hx)
    obtain ⟨z,hz,hzx⟩ := hk hx'
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hh := congrArg Subtype.val (mem_center_iff.mp hz (⟨y,hRK y.property⟩ : K))
    change (y : G) * (z : G) = (z : G) * (y : G) at hh
    change (y : G) * (x : G) = (x : G) * (y : G)
    change (z : G) = (x : G) at hzx
    rwa [hzx] at hh
  let : Group.IsSolvable (center R) := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  let : Group.IsSolvable g.ker :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hcentral)
  exact hR (Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [range_subtype]))
end Theory.GroupTheory
