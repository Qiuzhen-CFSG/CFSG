module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.GeneralizedFitting.AutomorphismSimple

/-!
# The inner subgroup and layer in the binary automorphism model

Inverse transpose carries a hyperplane radical to a point radical. Inner
conjugation preserves the dimension of the subspace recovered as common fixed
vectors, so inverse transpose is not inner in dimensions four and five. The
inner/graph coverage then gives exact index two. The actual matrix comparison
transports simplicity and perfectness, identifying the component layer with the
inner subgroup and supplying its canonical conjugation-compatible group model.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9 setup,
printed pp.389–390; the binary automorphism structure is GLS3, §2.5 and §2.7.
-/

@[expose] public section

open BinaryLinear BinaryLinear.OuterCyclic Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryNaturalDual.ModelOrbits.AutomorphismModel
variable {n : ℕ}
/-- Inverse transpose is not inner: it exchanges radicals with different fixed-space dimensions. -/
theorem graph_not_inner (hn : n = 4 ∨ n = 5) : graphLinear n ∉ MulAut.innerSubgroup (LinearGroup n) := by
  rintro ⟨g, hg⟩
  let i : Fin n := ⟨0, by omega⟩
  let f : OuterCyclic.Space n →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i
  have hf : f ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (fun _ => 1)
    exact one_ne_zero he
  obtain ⟨w, hw, he⟩ := graph_hyperplaneRadical hn f hf
  rw [← hg] at he
  change (radical f.ker).map (MulAut.conj g).toMonoidHom = radical (Submodule.span (ZMod 2) {w}) at he
  rw [radical_map_conj] at he
  have hd : Module.finrank (ZMod 2) f.range + Module.finrank (ZMod 2) f.ker = n := by
    simpa [OuterCyclic.Space] using f.finrank_range_add_finrank_ker
  have hr : Module.finrank (ZMod 2) f.range ≤ 1 := by
    simpa using Submodule.finrank_le f.range
  have hmap : f.ker.map g.toLinearMap ≠ ⊥ := by
    intro h
    have heq := g.finrank_map_eq f.ker
    rw [h] at heq
    simp only [finrank_bot] at heq
    omega
  have hline : Submodule.span (ZMod 2) {w} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hw
  have heq : f.ker.map g.toLinearMap = Submodule.span (ZMod 2) {w} := by
    ext v
    rw [mem_iff_fixed_radical hmap, mem_iff_fixed_radical hline, he]
  have heq' := g.finrank_map_eq f.ker
  rw [heq, finrank_span_singleton hw] at heq'
  omega

/-- The actual linear group over the binary field is centerless. -/
theorem linear_center_eq_bot (hn : 0 < n) : Subgroup.center (LinearGroup n) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  have hx : (slEquivLinear n).symm g ∈ Subgroup.center SL(n, ZMod 2) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply (slEquivLinear n).injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      (Subgroup.mem_center_iff.mp hg) (slEquivLinear n x)
  have hx1 : (slEquivLinear n).symm g = 1 := by
    simpa only [binary_center_eq_bot hn, Subgroup.mem_bot] using hx
  apply Subgroup.mem_bot.mpr
  apply (slEquivLinear n).symm.injective
  simpa using hx1

/-- Conjugation identifies the linear group with its actual inner subgroup. -/
noncomputable def innerEquiv (hn : 0 < n) :
    LinearGroup n ≃* MulAut.innerSubgroup (LinearGroup n) :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot (linear_center_eq_bot hn))

@[simp] theorem innerEquiv_apply (hn : 0 < n) (g : LinearGroup n) :
    (innerEquiv hn g).val = MulAut.conj g := rfl

/-- The inner subgroup has exactly index two, not merely cyclic quotient. -/
theorem inner_index (hn : n = 4 ∨ n = 5) :
    (MulAut.innerSubgroup (LinearGroup n)).index = 2 := by
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨graphLinear n, graph_not_inner hn, ?_⟩
  intro a
  obtain ⟨g, rfl | rfl⟩ := inner_graph hn a
  · exact Or.inr ⟨g, rfl⟩
  · left
    rw [← mul_assoc, ← pow_two, graphLinear_sq, one_mul]
    exact ⟨g, rfl⟩

/-- Higher-rank simplicity transported along the matrix action. -/
theorem linear_simple (hn : 3 ≤ n) : IsSimpleGroup (LinearGroup n) := by
  let := Atlas.psl_simple_high_rank (F := ZMod 2) n hn
  exact (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup

/-- Higher-rank perfectness transported along the matrix action. -/
theorem linear_perfect (hn : 3 ≤ n) : Group.IsPerfect (LinearGroup n) := by
  let := Atlas.psl_perfect (F := ZMod 2) n hn
  exact Group.IsPerfect.ofSurjective
    (f := (projectiveEquivLinear (by omega : 0 < n)).toMonoidHom)
    (projectiveEquivLinear (by omega : 0 < n)).surjective

/-- The inner subgroup is a component of the full automorphism group. -/
theorem inner_isComponent (hn : 3 ≤ n) :
    Theory.GroupTheory.IsComponent (MulAut (LinearGroup n))
      (MulAut.innerSubgroup (LinearGroup n)) := by
  let := linear_simple hn
  let := linear_perfect hn
  have hc := linear_center_eq_bot (by omega : 0 < n)
  let : Theory.GroupTheory.IsQuasisimple (LinearGroup n) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  exact ⟨Subgroup.Normal.isSubnormal inferInstance, Theory.GroupTheory.IsQuasisimple.of_mulEquiv (innerEquiv (by omega))⟩

/-- The actual component layer of the full automorphism group is its inner subgroup. -/
theorem layer_eq_inner (hn : 3 ≤ n) :
    Theory.GroupTheory.componentLayer (MulAut (LinearGroup n)) =
      MulAut.innerSubgroup (LinearGroup n) := by
  let := linear_simple hn
  apply le_antisymm
  · apply sSup_le
    intro K hK
    exact (hK.eq_innerSubgroup (linear_center_eq_bot (by omega))).le
  · exact le_sSup (inner_isComponent hn)

/-- The inner identification intertwines every automorphism with conjugation. -/
theorem innerEquiv_conjugation (hn : 0 < n) (a : MulAut (LinearGroup n))
    (g : LinearGroup n) :
    (innerEquiv hn (a g)).val = a * (innerEquiv hn g).val * a⁻¹ := by
  simp only [innerEquiv_apply]
  ext x
  simp

/-- Automorphism groups are compared through the actual projective-to-linear action. -/
noncomputable def projectiveAutEquiv (hn : 0 < n) :
    MulAut PSL(n, ZMod 2) ≃* MulAut (LinearGroup n) :=
  MulAut.congr (projectiveEquivLinear hn)

@[simp] theorem projectiveAutEquiv_inner (hn : 0 < n) (g : PSL(n, ZMod 2)) :
    projectiveAutEquiv hn (MulAut.conj g) = MulAut.conj (projectiveEquivLinear hn g) :=
  MulAut.congr_conj _ _

/-- The comparison preserves the actual inner subgroups. -/
theorem projectiveAutEquiv_map_inner (hn : 0 < n) :
    (MulAut.innerSubgroup PSL(n, ZMod 2)).map (projectiveAutEquiv hn).toMonoidHom =
      MulAut.innerSubgroup (LinearGroup n) :=
  MulAut.map_innerSubgroup_congr _

/-- The comparison intertwines automorphisms on the two concrete group models. -/
theorem projectiveAutEquiv_apply (hn : 0 < n) (a : MulAut PSL(n, ZMod 2))
    (g : PSL(n, ZMod 2)) :
    projectiveAutEquiv hn a (projectiveEquivLinear hn g) = projectiveEquivLinear hn (a g) := by
  change projectiveEquivLinear hn (a ((projectiveEquivLinear hn).symm
    (projectiveEquivLinear hn g))) = _
  rw [MulEquiv.symm_apply_apply]

private theorem map_layer_le {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom ≤ componentLayer H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro K hK
  exact Subgroup.map_le_iff_le_comap.mp (le_sSup (hK.map_equiv e))

private theorem map_layer {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom = componentLayer H := by
  apply le_antisymm (map_layer_le e)
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact Subgroup.map_le_iff_le_comap.mp (map_layer_le e.symm)

/-- The actual projective/linear comparison preserves the component layer. -/
theorem projectiveAutEquiv_map_layer (hn : 0 < n) :
    (componentLayer (MulAut PSL(n, ZMod 2))).map (projectiveAutEquiv hn).toMonoidHom =
      componentLayer (MulAut (LinearGroup n)) := map_layer _

/-- The layer of the actual projective automorphism group is its inner subgroup. -/
theorem projective_layer_eq_inner (hn : 3 ≤ n) :
    componentLayer (MulAut PSL(n, ZMod 2)) = MulAut.innerSubgroup PSL(n, ZMod 2) := by
  apply (Subgroup.map_injective
    (f := (projectiveAutEquiv (by omega : 0 < n)).toMonoidHom)
    (projectiveAutEquiv (by omega : 0 < n)).injective)
  rw [projectiveAutEquiv_map_layer, projectiveAutEquiv_map_inner, layer_eq_inner hn]

/-- The actual projective automorphism group also has inner index two. -/
theorem projective_inner_index (hn : n = 4 ∨ n = 5) :
    (MulAut.innerSubgroup PSL(n, ZMod 2)).index = 2 := by
  have h := Subgroup.index_map_of_bijective
    (f := (projectiveAutEquiv (by omega : 0 < n)).toMonoidHom)
    (projectiveAutEquiv (by omega : 0 < n)).bijective
    (MulAut.innerSubgroup PSL(n, ZMod 2))
  rw [projectiveAutEquiv_map_inner, inner_index hn] at h
  exact h.symm

end BinaryNaturalDual.ModelOrbits.AutomorphismModel
