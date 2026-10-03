module
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Conjugacy of roots of an involution

When all involutions are conjugate to `t`, an even-order element can be
conjugated so that its half-order power is `t`. Conversely, conjugacy between
two roots of `t` takes place inside `C(t)`: an ambient conjugator must fix the
unique involution in their cyclic subgroups.

These are the group-theoretic support arguments used in Wong (1964), Lemma 4
and the Appendix, DOI 10.1017/S1446788700022771.
-/

/-- Fuse the half-order power to put an even-order element in the root set of
the specified involution. -/
public theorem exists_isConj_involution_root
    {G : Type*} [Group G] [Finite G] (t : G)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t)
    (x : G) (hx : 2 ∣ orderOf x) :
    ∃ a : Subgroup.centralizer ({t} : Set G),
      t ∈ Subgroup.zpowers (a : G) ∧ IsConj x (a : G) := by
  let m := orderOf x / 2
  have hu : orderOf (x ^ m) = 2 :=
    orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos x)) hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfuse (x ^ m) hu)
  let e := MulAut.conj g
  have hp : (e x) ^ m = t := by
    rw [← map_pow]
    exact hg
  have ha : t ∈ Subgroup.zpowers (e x) := by
    rw [← hp]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hc : e x ∈ Subgroup.centralizer ({t} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← hp]
    exact (Commute.self_pow (e x) m).eq
  exact ⟨⟨e x, hc⟩, ha, isConj_iff.mpr ⟨g, rfl⟩⟩

/-- Roots of the same involution fuse in the ambient group precisely when
they fuse in its centralizer. -/
public theorem isConj_involution_roots_iff
    {G : Type*} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    (a b : Subgroup.centralizer ({t} : Set G))
    (ha : t ∈ Subgroup.zpowers (a : G))
    (hb : t ∈ Subgroup.zpowers (b : G)) :
    IsConj (a : G) (b : G) ↔ IsConj a b := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    let e := MulAut.conj g
    have het : e t ∈ Subgroup.zpowers (b : G) := by
      obtain ⟨n, hn⟩ := ha
      refine ⟨n, ?_⟩
      change (b : G) ^ n = e t
      change (a : G) ^ n = t at hn
      have he : e (a : G) = (b : G) := hg
      rw [← he, ← map_zpow, hn]
    have heqt : e t = t := by
      exact congrArg Subtype.val
        (IsCyclic.eq_of_orderOf_eq_two
          (x := (⟨e t, het⟩ : Subgroup.zpowers (b : G)))
          (y := (⟨t, hb⟩ : Subgroup.zpowers (b : G)))
          (by rw [← Subgroup.orderOf_coe, e.orderOf_eq, ht])
          (by rw [← Subgroup.orderOf_coe, ht]))
    have hc : g ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heqt)
    exact isConj_iff.mpr ⟨⟨g, hc⟩, Subtype.ext hg⟩
  · exact (Subgroup.centralizer ({t} : Set G)).subtype.map_isConj
