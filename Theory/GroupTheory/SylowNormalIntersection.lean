module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Sylow intersections with normal subgroups

In a finite group, the intersection of a Sylow `p`-subgroup with a normal
subgroup `E` is a Sylow `p`-subgroup of `E`. The statement uses `subgroupOf`
to express the intersection intrinsically in `E`; normality is essential.

Extend an arbitrary Sylow subgroup of `E` to an ambient Sylow subgroup,
then use Sylow conjugacy to carry the latter to the given subgroup. Normality
lets this conjugation restrict to an automorphism of `E`, carrying its
intrinsic Sylow subgroup to the required intersection.

This standard finite-group lemma supplies the intrinsic Sylow subgroup in
the normal product of rank-one factors used in Stellmacher (1.7), following
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

/-- A Sylow subgroup restricts to a Sylow subgroup of any normal subgroup. -/
public theorem Sylow.exists_subgroupOf_eq_of_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (E : Subgroup G) [E.Normal] :
    ∃ T : Sylow p E, (T : Subgroup E) = (S : Subgroup G).subgroupOf E := by
  obtain ⟨T₀⟩ := Sylow.nonempty (p := p) (G := E)
  obtain ⟨Q, hQ⟩ := T₀.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨(MulAut.conjNormal g : MulAut E) • T₀, ?_⟩
  ext x
  rw [← hg]
  change x ∈ (MulAut.conjNormal g : MulAut E) • (T₀ : Subgroup E) ↔
    (x : G) ∈ MulAut.conj g • (Q : Subgroup G)
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hQ]
  change ((MulAut.conjNormal g)⁻¹ x : G) ∈ (Q : Subgroup G) ↔
    (MulAut.conj g)⁻¹ (x : G) ∈ (Q : Subgroup G)
  rw [MulAut.conjNormal_inv_apply, ← map_inv, MulAut.conj_apply, inv_inv]
