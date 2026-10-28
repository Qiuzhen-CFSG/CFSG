module
public import Theory.Character.ClassFunction
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Vanishing on involution roots and on even-order elements

If all involutions are conjugate to t, every even-order element is conjugate
to an element of C(t) whose cyclic subgroup contains t. Thus a class function
vanishing on those roots vanishes on all even-order elements.

The conjugating element is obtained by fusing the half-order power. Conjugation
then transports that power and places the original element in the centralizer.
This is the fusion step in Wong (1964), Appendix p.106.
-/

/-- When all involutions are conjugate to `t`, every even-order element is
conjugate to a cyclic root of `t` in its centralizer. -/
public theorem exists_isConj_involution_root_of_even
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

public theorem classFunction_vanishes_even_of_involution_roots
    {G : Type*} [Group G] [Finite G] (t : G)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t)
    {f : ClassFunction G} (hf : IsClassFunction f)
    (hv : ∀ a : Subgroup.centralizer ({t} : Set G),
      t ∈ Subgroup.zpowers (a : G) → f a = 0)
    (x : G) (hx : 2 ∣ orderOf x) : f x = 0 := by
  obtain ⟨a, ha, hxa⟩ := exists_isConj_involution_root_of_even t hfuse x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hxa
  exact (hf x g).symm.trans (hg ▸ hv a ha)
