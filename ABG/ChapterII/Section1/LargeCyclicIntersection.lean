module
public import ABG.ChapterII.Section1.MaximalModels
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# Large cyclic intersections in a quasi-dihedral group

For a subgroup X of the quasi-dihedral presentation, the actual restriction
of ⟨a⟩ to X has index two when X is not contained in ⟨a⟩. When that restriction
has order at least eight, it is characteristic in X. These are the cyclic
subgroup inputs to the fusion analysis following ABG Chapter II, Section 1,
Lemma 1 in `refs/latex/alperin-brauer-gorenstein.tex`.

The intersection embeds in the cyclic subgroup, so it has a generator c.
Its order is at least eight and is unchanged by automorphisms of X. The
normal forms and the outer-square formula show that every element outside
⟨a⟩ has fourth power one. Thus every automorphism sends c into the intersection,
and hence preserves the whole intersection. The relative index formula
restricts the index-two cyclic maximal subgroup supplied by Lemma 1(iii).
The same presentation witnesses are used throughout; no finiteness instance
on the ambient group is needed for the characteristic assertion.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

/-- The cyclic intersection has index two whenever the subgroup is not cyclically contained. -/
public theorem cyclic_intersection_index_two {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card G = 2 ^ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (X : Subgroup G) (hX : ¬ X ≤ Subgroup.zpowers a) :
    ((Subgroup.zpowers a).subgroupOf X).index = 2 :=
  Subgroup.subgroupOf_index_eq_two _ _
    (explicit_subgroup_models hn a b hcard ha hb hab hgen).1 hX

/-- A cyclic intersection of order at least eight is characteristic in the containing subgroup. -/
public theorem large_cyclic_intersection_characteristic {n : ℕ} (hn : 4 ≤ n)
    (a b : G) (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (X : Subgroup G) (hA : 8 ≤ Nat.card ((Subgroup.zpowers a).subgroupOf X)) :
    ((Subgroup.zpowers a).subgroupOf X).Characteristic := by
  let A := (Subgroup.zpowers a).subgroupOf X
  let f : A →* Subgroup.zpowers a :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Subgroup.zpowers a => z.val) h))
  let : IsCyclic A := isCyclic_of_injective f hf
  obtain ⟨c, hc⟩ := Subgroup.isCyclic_iff_exists_zpowers_eq_top A |>.mp inferInstance
  have hco : 8 ≤ orderOf c := by
    have he : Nat.card A = orderOf c := by rw [← hc, Nat.card_zpowers]
    exact he ▸ hA
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e
  change A.map e.toMonoidHom ≤ A
  conv_lhs => rw [← hc, MonoidHom.map_zpowers]
  apply Subgroup.zpowers_le.mpr
  have hmem : (e c).val ∈ Subgroup.zpowers a := by
    by_contra hnot
    have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    obtain ⟨i, hi, hi' | hi'⟩ := normal_form a b _ _ (by positivity) ha hb2 hab hgen (e c).val
    · exact hnot (hi' ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    have hpow : (e c).val ^ 4 = 1 := by
      rw [hi', show 4 = 2 * 2 by decide, pow_mul, outer_square hn a b hb hab, ← pow_mul]
      have he : 2 ^ (n - 2) * i * 2 = 2 ^ (n - 1) * i := by
        rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
        ring
      rw [he, ← ha, pow_mul, pow_orderOf_eq_one, one_pow]
    have ho : orderOf ((e c).val) ≤ 4 := orderOf_le_of_pow_eq_one (by decide) hpow
    change orderOf (X.subtype (e.toMonoidHom c)) ≤ 4 at ho
    rw [orderOf_injective X.subtype X.subtype_injective, orderOf_injective e.toMonoidHom e.injective] at ho
    omega
  exact hmem
end ABG.QuasiDihedral
