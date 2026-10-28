module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent.RootCells
public import Mathlib.Data.List.Forall2

/-!
# Ordered products and the two inversion factors

Partition a finite family of positive root subgroups according to whether
conjugation by `n` takes them into the positive or negative subgroup. An
arbitrary-order product theorem, applied with the retained roots first,
then gives the local `n*q = a*n*v` collection used in root Bruhat forms.
Generation by the root subgroups is not substituted for ordered products.

The lemma is stated for subgroups so that it applies to the actual root
subgroups without choosing or normalizing their parametrizations.

Source: GLS3 1.12.7(a) and 1.11.5, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells

variable {X ι : Type*} [Group X]

private theorem product_mem_of_forall₂ (A : ι → Subgroup X) (H : Subgroup X)
    {roots : List ι} {xs : List X}
    (hxs : List.Forall₂ (fun i x => x ∈ A i) roots xs)
    (hA : ∀ i ∈ roots, A i ≤ H) : xs.prod ∈ H := by
  induction hxs with
  | nil => exact H.one_mem
  | @cons i x roots xs hx hxs ih =>
    exact H.mul_mem (hA i (by simp) hx) (ih (fun j hj => hA j (by simp [hj])))

/-- An arbitrary-order positive product gives the two ordered inversion
factors, retaining the literal conjugation map and the normalizer element. -/
theorem split_of_ordered_products
    (U V : Subgroup X) (A : ι → Subgroup X) (P : Set ι)
    (roots : List ι) (hnd : roots.Nodup) (hroots : ∀ i, i ∈ roots ↔ i ∈ P)
    (hU : ∀ i ∈ P, A i ≤ U)
    (hproduct : ∀ order : List ι, order.Nodup →
      (∀ i, i ∈ order ↔ i ∈ P) → ∀ q ∈ U,
        ∃ xs : List X, List.Forall₂ (fun i x => x ∈ A i) order xs ∧ xs.prod = q)
    (n : X)
    (htransport : ∀ i ∈ P,
      A i ≤ U.comap (MulAut.conj n).toMonoidHom ∨
      A i ≤ V.comap (MulAut.conj n).toMonoidHom)
    (q : X) (hq : q ∈ U) :
    ∃ a ∈ U, ∃ v ∈ rightFactor U V n, n * q = a * n * v := by
  classical
  let p : ι → Bool := fun i => decide (A i ≤ U.comap (MulAut.conj n).toMonoidHom)
  let left := roots.filter p
  let right := roots.filter (fun i => !p i)
  have hleft : ∀ i, i ∈ left ↔ i ∈ P ∧
      A i ≤ U.comap (MulAut.conj n).toMonoidHom := by
    intro i
    simp only [left, List.mem_filter, p, decide_eq_true_eq, hroots]
  have hright : ∀ i, i ∈ right ↔ i ∈ P ∧
      ¬A i ≤ U.comap (MulAut.conj n).toMonoidHom := by
    intro i
    simp only [right, List.mem_filter, p, Bool.not_eq, ne_eq, decide_eq_true_eq, hroots]
  have horder : (left ++ right).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨hnd.filter p, hnd.filter (fun i => !p i), ?_⟩
    rw [List.disjoint_left]
    intro i hi hj
    exact ((hright i).mp hj).2 ((hleft i).mp hi).2
  have hmem : ∀ i, i ∈ left ++ right ↔ i ∈ P := by
    intro i
    rw [List.mem_append, hleft, hright]
    tauto
  obtain ⟨xs, hxs, hprod⟩ := hproduct (left ++ right) horder hmem q hq
  let ys := xs.take left.length
  let zs := xs.drop left.length
  have hys : List.Forall₂ (fun i x => x ∈ A i) left ys := by
    have h := List.forall₂_take left.length hxs
    simpa only [List.take_left] using h
  have hzs : List.Forall₂ (fun i x => x ∈ A i) right zs := by
    have h := List.forall₂_drop left.length hxs
    simpa only [List.drop_left] using h
  have hr : ys.prod ∈ U.comap (MulAut.conj n).toMonoidHom :=
    product_mem_of_forall₂ A _ hys (fun i hi => ((hleft i).mp hi).2)
  have hvU : zs.prod ∈ U :=
    product_mem_of_forall₂ A U hzs (fun i hi => hU i ((hright i).mp hi).1)
  have hvV : zs.prod ∈ V.comap (MulAut.conj n).toMonoidHom :=
    product_mem_of_forall₂ A _ hzs (fun i hi =>
      (htransport i ((hright i).mp hi).1).resolve_left ((hright i).mp hi).2)
  have heq : q = ys.prod * zs.prod := by
    rw [← hprod, ← List.prod_append]
    exact congrArg List.prod (List.take_append_drop left.length xs).symm
  refine ⟨n * ys.prod * n⁻¹, hr, zs.prod, ⟨hvU, hvV⟩, ?_⟩
  rw [heq]
  group

end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells
end
