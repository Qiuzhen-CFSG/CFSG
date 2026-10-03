module

public import Theory.GroupTheory.SubgroupEnumeration
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Exhaustive descending subgroup certificates

For an upward-closed, conjugacy-invariant property, a family containing the
whole finite group and representing every eligible maximal subgroup of each
entry represents every subgroup with that property. Induction upwards in the
finite subgroup lattice proves completeness. In particular, centric subgroups
can be enumerated by descending through maximal subgroups and discarding
noncentric entries. A separate local exclusion test need not be upward-closed
and must not be used to prune this descent without an additional proof.

Source: the elementary maximal-chain argument in the finite subgroup lattice;
this is the descending counterpart of `SubgroupEnumeration`.
-/

namespace Theory.GroupTheory.SubgroupEnumeration
variable {G : Type*} [Group G] {ι : Type*}

/-- Descending through every eligible maximal subgroup gives exhaustive coverage. -/
public theorem represented_of_maximal_descent [Finite G] (K : ι → Subgroup G) (P : Subgroup G → Prop)
    (hmono : Monotone P)
    (hconj : ∀ H g, P H → P (H.map (MulAut.conj g).toMonoidHom))
    (htop : ∃ i, K i = ⊤)
    (hstep : ∀ i H, H ⋖ K i → P H → Represented K H)
    (H : Subgroup G) (hH : P H) : Represented K H := by
  classical
  let : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  induction H using (wellFounded_gt (α := Subgroup G)).induction with
  | h H ih =>
    by_cases ht : H = ⊤
    · obtain ⟨i, hi⟩ := htop
      exact ⟨i, 1, by simpa [ht] using hi.symm⟩
    · obtain ⟨V, hHV, _⟩ := exists_covBy_le_of_lt (lt_top_iff_ne_top.mpr ht)
      obtain ⟨i, g, hg⟩ := ih V hHV.lt (hmono hHV.le hH)
      have hcov : H.map (MulAut.conj g).toMonoidHom ⋖ K i := by
        rw [← hg]
        exact (apply_covBy_apply_iff (MulAut.conj g).mapSubgroup).mpr hHV
      obtain ⟨j, k, hk⟩ := hstep i _ hcov (hconj H g hH)
      refine ⟨j, k * g, ?_⟩
      rw [← hk, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]

/-- The same descent works below any chosen starting subgroup. The property
must be upward-closed, but need not hold for subgroups outside that interval. -/
public theorem represented_of_maximal_descent_below [Finite G]
    (K : ι → Subgroup G) (A : Subgroup G) (P : Subgroup G → Prop)
    (hmono : Monotone P)
    (hconj : ∀ H g, P H → P (H.map (MulAut.conj g).toMonoidHom))
    (hbase : ∃ i, K i = A)
    (hstep : ∀ i H, H ⋖ K i → P H → Represented K H)
    (H : Subgroup G) (hHA : H ≤ A) (hH : P H) : Represented K H := by
  classical
  let : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  induction H using (wellFounded_gt (α := Subgroup G)).induction with
  | h H ih =>
    by_cases ht : H = A
    · obtain ⟨i, hi⟩ := hbase
      refine ⟨i, 1, ?_⟩
      have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      simpa only [he, Subgroup.map_id, ht] using hi.symm
    · obtain ⟨V, hHV, hVA⟩ := exists_covBy_le_of_lt (lt_of_le_of_ne hHA ht)
      obtain ⟨i, g, hg⟩ := ih V hHV.lt hVA (hmono hHV.le hH)
      have hcov : H.map (MulAut.conj g).toMonoidHom ⋖ K i := by
        rw [← hg]
        exact (apply_covBy_apply_iff (MulAut.conj g).mapSubgroup).mpr hHV
      obtain ⟨j, k, hk⟩ := hstep i _ hcov (hconj H g hH)
      refine ⟨j, k * g, ?_⟩
      rw [← hk, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]


/-- Every overgroup of a centric subgroup is centric. -/
public theorem centralizer_le_of_le {H K : Subgroup G} (h : H ≤ K)
    (hc : Subgroup.centralizer (H : Set G) ≤ H) :
    Subgroup.centralizer (K : Set G) ≤ K :=
  (Subgroup.centralizer_le h).trans (hc.trans h)

/-- Automorphisms preserve centricity. -/
public theorem centralizer_le_map (H : Subgroup G) (e : MulAut G)
    (hc : Subgroup.centralizer (H : Set G) ≤ H) :
    Subgroup.centralizer (H.map e.toMonoidHom : Set G) ≤ H.map e.toMonoidHom := by
  intro x hx
  refine Subgroup.mem_map.mpr ⟨e.symm x, hc ?_, e.apply_symm_apply x⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  apply e.injective
  simpa using (Subgroup.mem_centralizer_iff.mp hx) (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)
/-- Centricity alone is a valid pruning condition for maximal-subgroup descent. -/
public theorem represented_centric_of_maximal_descent [Finite G]
    (K : ι → Subgroup G) (htop : ∃ i, K i = ⊤)
    (hstep : ∀ i H, H ⋖ K i → Subgroup.centralizer (H : Set G) ≤ H → Represented K H)
    (H : Subgroup G) (hH : Subgroup.centralizer (H : Set G) ≤ H) : Represented K H :=
  represented_of_maximal_descent K (fun H => Subgroup.centralizer (H : Set G) ≤ H)
    (fun _ _ h => centralizer_le_of_le h) (fun H g => centralizer_le_map H (MulAut.conj g))
    htop hstep H hH

end Theory.GroupTheory.SubgroupEnumeration
