module

public import Theory.AlgebraicGroup.ClosedSubgroup.Product
public import Theory.AlgebraicGroup.Semisimple.Defs

/-!
This module provides the component-family interface and its proved elementary
group-theoretic consequences used by GLS3 Theorem 1.7.2(d).
-/

universe u

/-!
  Component-family infrastructure for the semisimple part of GLS3 A4.

  The source theorem eventually obtains such a family from the irreducible
  orthogonal blocks of a root system.  That root-to-group construction is not
  present in the maintained baseline, so this module records the purely
  group-theoretic consequences separately.  In particular, the centre
  direction below uses only the component decomposition and pairwise
  commutation; it does not smuggle in the missing existence theorem.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k]

/-! A finite family of closed simple subgroups with a product decomposition. -/

public structure IsSemisimpleComponentFamily
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} (components : Fin n → ClosedSubgroup G) : Prop where
  simple : ∀ i, IsSimpleAlgebraicGroup (components i).carrierVariety
  factorization : ∀ x : Variety.Point G,
    ∃ factors : Fin n → Variety.Point G,
      (∀ i, factors i ∈ components i) ∧
        x = (List.ofFn factors).prod
  commute : ∀ i j, i ≠ j →
    ⁅(components i).toSubgroup, (components j).toSubgroup⁆ = ⊥

namespace IsSemisimpleComponentFamily

private lemma conj_mem_of_factor
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (i : Fin n) {a x : Variety.Point G}
    (ha : ∃ j, a ∈ components j ∧ x ∈ components i) :
    a * x * a⁻¹ ∈ components i := by
  rcases ha with ⟨j, haj, hxi⟩
  by_cases hij : i = j
  · subst j
    exact (components i).toSubgroup.mul_mem
      ((components i).toSubgroup.mul_mem haj hxi)
      ((components i).toSubgroup.inv_mem haj)
  · have hcentralizer :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hfamily.commute j i (fun h => hij h.symm))
    have hcomm : Commute a x :=
      (Subgroup.mem_centralizer_iff.mp
        (hcentralizer haj) x hxi).symm
    have heq : a * x * a⁻¹ = x := by
      calc
        a * x * a⁻¹ = x * a * a⁻¹ := by rw [hcomm.eq]
        _ = x := by simp
    rw [heq]
    exact hxi

private lemma conj_mem_list_prod
    {G : Variety k} [AlgebraicGroup G]
    {H : Subgroup (Variety.Point G)}
    {l : List (Variety.Point G)}
    (hfactor : ∀ a ∈ l, ∀ x, x ∈ H → a * x * a⁻¹ ∈ H)
    {x : Variety.Point G} (hx : x ∈ H) :
    l.prod * x * l.prod⁻¹ ∈ H := by
  induction l with
  | nil => simpa using hx
  | cons a l ih =>
      rw [List.prod_cons, mul_inv_rev]
      have hinner : l.prod * x * l.prod⁻¹ ∈ H := by
        apply ih
        intro b hb y hy
        exact hfactor b (by simp [hb]) y hy
      simpa [mul_assoc] using hfactor a (by simp) _ hinner

private lemma list_prod_mem_of_mem
    {G : Type u} [Group G] {H : Subgroup G} {l : List G}
    (hl : ∀ a ∈ l, a ∈ H) : l.prod ∈ H := by
  induction l with
  | nil => exact H.one_mem
  | cons a l ih =>
      rw [List.prod_cons]
      exact H.mul_mem (hl a (by simp))
        (ih (fun b hb => hl b (by simp [hb])))

private lemma commute_of_ofFn_prod_of_ne
    {G : Type u} [Group G] {n : ℕ} (f : Fin n → G)
    (i : Fin n) (x : G)
    (hother : ∀ j, j ≠ i → Commute (f j) x)
    (hprod : Commute (List.ofFn f).prod x) :
    Commute (f i) x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      revert hother hprod
      refine Fin.cases ?_ ?_ i
      · intro hother hprod
        rw [List.ofFn_succ] at hprod
        let tail : Fin n → G := fun j => f j.succ
        have htail : Commute (List.ofFn tail).prod x := by
          apply Commute.list_prod_left
          intro a ha
          rw [List.mem_ofFn] at ha
          rcases ha with ⟨j, rfl⟩
          apply hother j.succ
          intro h
          exact (Fin.succ_ne_zero j) h
        have hEq : f 0 * x * (List.ofFn tail).prod =
            x * f 0 * (List.ofFn tail).prod := by
          calc
            f 0 * x * (List.ofFn tail).prod =
                f 0 * ((List.ofFn tail).prod * x) := by
                  rw [mul_assoc, htail.eq]
            _ = x * f 0 * (List.ofFn tail).prod := by
              simpa [mul_assoc] using hprod.eq
        exact mul_right_cancel hEq
      · intro j hother hprod
        rw [List.ofFn_succ] at hprod
        let tail : Fin n → G := fun l => f l.succ
        have hhead : Commute (f 0) x := hother 0 (by
          intro h
          exact (Fin.succ_ne_zero j) h.symm)
        have hEq : f 0 * ((List.ofFn tail).prod * x) =
            f 0 * (x * (List.ofFn tail).prod) := by
          calc
            f 0 * ((List.ofFn tail).prod * x) =
                (f 0 * (List.ofFn tail).prod) * x := by simp [mul_assoc]
            _ = x * (f 0 * (List.ofFn tail).prod) := by
              simpa [mul_assoc] using hprod.eq
            _ = (x * f 0) * (List.ofFn tail).prod := by simp [mul_assoc]
            _ = (f 0 * x) * (List.ofFn tail).prod := by rw [hhead.eq]
            _ = f 0 * (x * (List.ofFn tail).prod) := by simp [mul_assoc]
        have htail : Commute (List.ofFn tail).prod x :=
          mul_left_cancel hEq
        have hotherTail : ∀ l, l ≠ j → Commute (tail l) x := by
          intro l hlj
          apply hother l.succ
          intro h
          apply hlj
          exact (Fin.succ_injective n) (by simpa using h)
        simpa [tail] using ih tail j hotherTail htail

/-!
  A factorization by pairwise commuting component subgroups already forces
  each component to be normal in the ambient point group.  This is the
  elementary group-theoretic part of the component theorem; the root-system
  argument is only needed to construct the family in the first place.
-/

public lemma component_normal
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (i : Fin n) :
    (components i).toSubgroup.Normal := by
  refine ⟨?_⟩
  intro x hx y
  rcases hfamily.factorization y with ⟨factors, hfac, rfl⟩
  apply conj_mem_list_prod
  · intro a ha z hz
    rw [List.mem_ofFn] at ha
    rcases ha with ⟨j, rfl⟩
    exact conj_mem_of_factor hfamily i ⟨j, hfac j, hz⟩
  · exact hx

/-! The component subgroups generate the ambient point group. -/

public lemma components_iSup_eq_top
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components) :
    ⨆ i, (components i).toSubgroup = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  rcases hfamily.factorization x with ⟨factors, hfactors, rfl⟩
  apply list_prod_mem_of_mem
  intro a ha
  rw [List.mem_ofFn] at ha
  rcases ha with ⟨i, rfl⟩
  exact le_iSup (fun j => (components j).toSubgroup) i (hfactors i)

/-! Distinct components meet only in the ambient centre. -/

public lemma pairwise_intersection_le_center
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    {i j : Fin n} (hij : i ≠ j) :
    (components i).toSubgroup ⊓ (components j).toSubgroup ≤
      Subgroup.center (Variety.Point G) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  rcases hfamily.factorization y with ⟨factors, hfactors, rfl⟩
  apply Commute.list_prod_left
  intro a ha
  rw [List.mem_ofFn] at ha
  rcases ha with ⟨l, rfl⟩
  by_cases hil : l = i
  · subst l
    have hcentralizer :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hfamily.commute j i hij.symm)
    exact Subgroup.mem_centralizer_iff.mp
      (hcentralizer hx.2) (factors i) (hfactors i)
  · by_cases hjl : l = j
    · subst l
      have hcentralizer :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (hfamily.commute i j hij)
      exact Subgroup.mem_centralizer_iff.mp
        (hcentralizer hx.1) (factors j) (hfactors j)
    · have hcentralizer :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (hfamily.commute i l (fun h => hil h.symm))
      exact Subgroup.mem_centralizer_iff.mp
        (hcentralizer hx.1) (factors l) (hfactors l)

/-! The centre of one component embeds into the ambient centre. -/

public lemma component_center_le_ambient_center
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (i : Fin n) {z : Variety.Point G}
    (hz : z ∈ components i)
    (hzc : ∀ y, y ∈ components i → Commute z y) :
    z ∈ Subgroup.center (Variety.Point G) := by
  rw [Subgroup.mem_center_iff]
  intro y
  rcases hfamily.factorization y with ⟨factors, hfactors, rfl⟩
  have hprod : Commute (List.ofFn factors).prod z := by
    apply Commute.list_prod_left
    intro a ha
    rw [List.mem_ofFn] at ha
    rcases ha with ⟨j, rfl⟩
    by_cases hij : i = j
    · subst j
      exact (hzc (factors i) (hfactors i)).symm
    · have hcentralizer :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (hfamily.commute i j hij)
      exact (Subgroup.mem_centralizer_iff.mp
        (hcentralizer hz) (factors j) (hfactors j))
  exact hprod.eq

/-!
  A product of elements central in their respective components is central in
  the ambient group.  This is the centre direction that is independent of the
  unresolved root-block construction.
-/

public lemma product_mem_center
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (zs : Fin n → Variety.Point G)
    (hzs : ∀ i, zs i ∈ components i ∧
      ∀ y, y ∈ components i → Commute (zs i) y) :
    (List.ofFn zs).prod ∈ Subgroup.center (Variety.Point G) := by
  rw [Subgroup.mem_center_iff]
  intro y
  rcases hfamily.factorization y with ⟨ys, hys, hy⟩
  have hEach : ∀ i, Commute (zs i) y := by
    intro i
    rw [hy]
    apply Commute.list_prod_right
    intro yj hyj
    rw [List.mem_ofFn] at hyj
    rcases hyj with ⟨j, rfl⟩
    by_cases hij : i = j
    · subst j
      exact hzs i |>.2 (ys i) (hys i)
    · have hcentralizer :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (hfamily.commute i j hij)
      exact (Subgroup.mem_centralizer_iff.mp
        (hcentralizer (hzs i).1) (ys j) (hys j)).symm
  exact (Commute.list_prod_left (List.ofFn zs) y (by
    intro zi hzi
    rw [List.mem_ofFn] at hzi
    rcases hzi with ⟨i, rfl⟩
    exact hEach i)).eq.symm

/-!
  The preceding implication has a converse at the level of a fixed
  factorization: an ambient-central product has each of its factors central
  in its own component.  The proof is cancellation in the finite product;
  pairwise commutation removes all factors except the selected one.
-/

public lemma factors_mem_center_of_product_mem_center
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (factors : Fin n → Variety.Point G)
    (hfactors : ∀ i, factors i ∈ components i)
    (hz : (List.ofFn factors).prod ∈ Subgroup.center (Variety.Point G)) :
    ∀ i, ∀ y, y ∈ components i → Commute (factors i) y := by
  intro i y hy
  apply commute_of_ofFn_prod_of_ne factors i y
  · intro j hji
    have hcentralizer :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hfamily.commute j i hji)
    exact (Subgroup.mem_centralizer_iff.mp
      (hcentralizer (hfactors j)) y hy).symm
  · exact (Subgroup.mem_center_iff.mp hz y).symm

public lemma product_mem_center_iff
    {G : Variety k} [AlgebraicGroup G]
    {n : ℕ} {components : Fin n → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (factors : Fin n → Variety.Point G)
    (hfactors : ∀ i, factors i ∈ components i) :
    (List.ofFn factors).prod ∈ Subgroup.center (Variety.Point G) ↔
      ∀ i, ∀ y, y ∈ components i → Commute (factors i) y := by
  constructor
  · exact factors_mem_center_of_product_mem_center hfamily factors hfactors
  · intro hcentral
    exact product_mem_center hfamily factors (fun i => ⟨hfactors i, hcentral i⟩)

end IsSemisimpleComponentFamily

/-!
  The product-density step used in the source component theorem.  Packaging
  it with the subgroup join keeps the geometric input (`Dense`) explicit while
  eliminating the routine subgroup bookkeeping from later component proofs.
-/

public lemma closedSubgroup_sup_eq_top_of_dense_product
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    [Nonempty (Variety.Point G)] [PreirreducibleSpace (Variety.Point G)]
    (hconnected : _root_.IsConnected (Set.univ : Set (Variety.Point G)))
    (S T : ClosedSubgroup G)
    (hdense : Dense
      ((S.toSubgroup : Set (Variety.Point G)) *
        (T.toSubgroup : Set (Variety.Point G)))) :
    S.toSubgroup ⊔ T.toSubgroup = ⊤ := by
  apply closedSubgroup_product_dense_contained_subgroup_eq_top
    (S.toSubgroup ⊔ T.toSubgroup) S T hconnected le_sup_left le_sup_right
  exact hdense

end Theory.AlgebraicGroup
