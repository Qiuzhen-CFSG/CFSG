module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Geometry

/-!
# Rigidity of binary point-radical geometry

An automorphism of the binary linear group that preserves point radicals is
inner. The radicals determine a permutation of the nonzero vectors; adjoining
zero gives a bijection equivariant for the automorphism and the natural action.
The common fixed space of the radical of a binary span forces this bijection
to preserve sums. It therefore defines a linear equivalence, and equivariance
identifies the original automorphism with conjugation by that equivalence.

This proves the conditional geometric reconstruction step for the binary
specialization of GLS3, Theorem 2.5.12 and §2.7; see
`refs/KGroup/GLS3/chapter2.tex`, especially lines 1111–1115. The separate
assertion that arbitrary automorphisms preserve point radicals after a possible
inverse transpose is not a premise discharged here.
-/

namespace BinaryLinear.OuterCyclic

private theorem conj_mem_pointRadical {n : ℕ} (g : LinearGroup n) (v : Space n)
    {t : LinearGroup n} (ht : t ∈ pointRadical n v) :
    MulAut.conj g t ∈ pointRadical n (g v) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change g (t (g.symm (c • g v))) = c • g v
    rw [map_smul, LinearEquiv.symm_apply_apply, map_smul,
      ht.1 v (Submodule.mem_span_singleton_self v), map_smul]
  · intro w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (ht.2 (g.symm w))
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    have h := congrArg g hc
    simpa only [map_smul, map_sub, LinearEquiv.apply_symm_apply, MulAut.conj_apply,
      LinearEquiv.mul_apply, LinearEquiv.coe_inv] using h

private theorem map_pointRadical_conj {n : ℕ} (g : LinearGroup n) (v : Space n) :
    (pointRadical n v).map (MulAut.conj g).toMonoidHom = pointRadical n (g v) := by
  apply le_antisymm
  · rintro t ⟨s, hs, rfl⟩
    exact conj_mem_pointRadical g v hs
  · intro t ht
    refine ⟨MulAut.conj g⁻¹ t, ?_, ?_⟩
    · change MulAut.conj g⁻¹ t ∈ pointRadical n v
      simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
        conj_mem_pointRadical g⁻¹ (g v) ht
    · simp [MulAut.conj_apply, mul_assoc]

private noncomputable def pointMap {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) (v : Space n) : Space n :=
  if hv : v = 0 then 0 else (ha v hv).choose

private theorem pointMap_zero {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) : pointMap a ha 0 = 0 := by
  simp [pointMap]

private theorem pointMap_spec {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) {v : Space n} (hv : v ≠ 0) :
    pointMap a ha v ≠ 0 ∧
      (pointRadical n v).map a.toMonoidHom = pointRadical n (pointMap a ha v) := by
  simpa only [pointMap, dif_neg hv] using (ha v hv).choose_spec

private theorem pointMap_injective {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) : Function.Injective (pointMap a ha) := by
  intro v w h
  by_cases hv : v = 0
  · subst v
    by_contra hw
    exact (pointMap_spec a ha (Ne.symm hw)).1 (h.symm.trans (pointMap_zero a ha))
  by_cases hw : w = 0
  · subst w
    exact False.elim ((pointMap_spec a ha hv).1 (h.trans (pointMap_zero a ha)))
  apply pointRadical_injective hv hw
  apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
  rw [(pointMap_spec a ha hv).2, (pointMap_spec a ha hw).2, h]

/-- Conjugation of radicals makes the induced vector map equivariant. -/
private theorem pointMap_equivariant {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) (g : LinearGroup n) (v : Space n) :
    pointMap a ha (g v) = a g (pointMap a ha v) := by
  by_cases hv : v = 0
  · subst v
    simp [pointMap_zero]
  have hgv : g v ≠ 0 := fun h => hv (g.map_eq_zero_iff.mp h)
  have hfv := (pointMap_spec a ha hv).1
  apply pointRadical_injective (pointMap_spec a ha hgv).1
    (fun h => hfv ((a g).map_eq_zero_iff.mp h))
  calc
    pointRadical n (pointMap a ha (g v)) =
        (pointRadical n (g v)).map a.toMonoidHom := (pointMap_spec a ha hgv).2.symm
    _ = ((pointRadical n v).map a.toMonoidHom).map
        (MulAut.conj (a g)).toMonoidHom := by
      rw [← map_pointRadical_conj, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext t
      simp [MulAut.conj_apply]
    _ = pointRadical n (a g (pointMap a ha v)) := by
      rw [(pointMap_spec a ha hv).2, map_pointRadical_conj]

private theorem binary_add_self {n : ℕ} (v : Space n) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private theorem mem_binary_span_pair {n : ℕ} {x y z : Space n}
    (hz : z ∈ Submodule.span (ZMod 2) {x, y}) :
    z = 0 ∨ z = x ∨ z = y ∨ z = x + y := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hz
  have binary (c : ZMod 2) : c = 0 ∨ c = 1 :=
    (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases binary c with rfl | rfl <;> rcases binary d with rfl | rfl <;> simp

private theorem pointMap_add {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) (x y : Space n) :
    pointMap a ha (x + y) = pointMap a ha x + pointMap a ha y := by
  by_cases hx : x = 0
  · subst x
    simp [pointMap_zero]
  by_cases hy : y = 0
  · subst y
    simp [pointMap_zero]
  by_cases hxy : x = y
  · subst y
    simp only [binary_add_self, pointMap_zero]
  let W := Submodule.span (ZMod 2) {pointMap a ha x, pointMap a ha y}
  have hfx : pointMap a ha x ∈ W := Submodule.subset_span (by simp)
  have hfy : pointMap a ha y ∈ W := Submodule.subset_span (by simp)
  have hW : W ≠ ⊥ := by
    intro h
    exact (pointMap_spec a ha hx).1 (by simpa only [h, Submodule.mem_bot] using hfx)
  -- Every element of the radical of W fixes both images. Its inverse image
  -- under a fixes x and y, hence x + y; equivariance then recovers W.
  have hsum : pointMap a ha (x + y) ∈ W := by
    apply (mem_iff_fixed_radical hW _).mpr
    intro g hg
    have hax : a.symm g x = x := by
      apply pointMap_injective a ha
      rw [pointMap_equivariant, a.apply_symm_apply, hg.1 _ hfx]
    have hay : a.symm g y = y := by
      apply pointMap_injective a ha
      rw [pointMap_equivariant, a.apply_symm_apply, hg.1 _ hfy]
    have h := pointMap_equivariant a ha (a.symm g) (x + y)
    simpa only [map_add, hax, hay, a.apply_symm_apply] using h.symm
  rcases mem_binary_span_pair hsum with hz | he | he | he
  · have h : x + y = 0 := pointMap_injective a ha (hz.trans (pointMap_zero a ha).symm)
    have h' := congrArg (fun z => z + y) h
    exact False.elim (hxy (by simpa only [add_assoc, binary_add_self, add_zero, zero_add] using h'))
  · exact False.elim (hy (add_eq_left.mp (pointMap_injective a ha he)))
  · exact False.elim (hx (add_eq_right.mp (pointMap_injective a ha he)))
  · exact he

private theorem point_rigidity {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) : ∃ g : LinearGroup n, a = MulAut.conj g := by
  let f : Space n →ₗ[ZMod 2] Space n :=
    { toFun := pointMap a ha
      map_add' := pointMap_add a ha
      map_smul' := by
        intro c v
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · simp [pointMap_zero]
        · simp }
  have hf : Function.Bijective f :=
    ⟨pointMap_injective a ha, Finite.surjective_of_injective (pointMap_injective a ha)⟩
  let g : LinearGroup n := LinearEquiv.ofBijective f hf
  refine ⟨g, ?_⟩
  apply MulEquiv.ext
  intro t
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := g.surjective v
  change a t (g w) = g (t (g.symm (g w)))
  rw [LinearEquiv.symm_apply_apply]
  exact (pointMap_equivariant a ha t w).symm

/-- For the binary groups of dimensions four and five, preservation of point
radicals forces an automorphism to be conjugation by a linear equivalence. -/
public theorem eq_conj_of_preservesPointRadicals {n : ℕ} (hn : n = 4 ∨ n = 5)
    (a : MulAut (LinearGroup n)) (ha : PreservesPointRadicals a) :
    ∃ g : LinearGroup n, a = MulAut.conj g := by
  rcases hn with rfl | rfl <;> exact point_rigidity a ha

end BinaryLinear.OuterCyclic
