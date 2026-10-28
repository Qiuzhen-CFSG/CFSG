module

public import Theory.GroupTheory.FixedOrderedProduct
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Products around a root orbit

An endomorphism cyclically permutes the iterates of a periodic element.
If the first factor commutes with the others, their ordered product is fixed.
Injectivity of the ordered subgroup product makes it nonidentity whenever the
original element is nonidentity. This step does not require the ambient radical
or a whole relative root group to be abelian.

The consumer in `ProperParabolicFixedRadical` uses a single orbit of absolute
root subgroups. Repeating an orbit to the order of the whole root permutation
is insufficient: repetition can kill the product in defining characteristic.

Source: the root-orbit products in GLS3, Chapter 2, §§2.3–2.4.
-/

namespace Theory.AlgebraicGroup.ProperParabolicFixedRadical

variable {G : Type*} [Group G]

/-- Multiply one finite sequence of iterates in its given order. -/
@[expose] public def orbitProduct (σ : G →* G) (m : ℕ) (x : G) : G :=
  (List.ofFn fun i : Fin m => (σ^[i.val]) x).prod

/-- Closing the cycle gives a fixed product when its first factor commutes
with the other factors. The ambient group need not be commutative. -/
public theorem orbitProduct_fixed (σ : G →* G) (m : ℕ) (x : G)
    (hperiod : (σ^[m]) x = x)
    (hcomm : ∀ i < m, Commute x ((σ^[i]) x)) :
    σ (orbitProduct σ m x) = orbitProduct σ m x := by
  cases m with
  | zero => simp [orbitProduct]
  | succ n =>
    have ht : Commute x
        (List.ofFn fun i : Fin n => (σ^[i.val + 1]) x).prod := by
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact hcomm (i.val + 1) (by omega)
    change σ (List.ofFn fun i : Fin (n + 1) => (σ^[i.val]) x).prod = _
    rw [MonoidHom.map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, ← Function.iterate_succ_apply']
    rw [List.ofFn_succ', List.prod_concat]
    change (List.ofFn fun i : Fin n => (σ^[i.val + 1]) x).prod *
      (σ^[n + 1]) x = _
    rw [hperiod]
    unfold orbitProduct
    rw [List.ofFn_succ, List.prod_cons]
    exact ht.eq.symm

/-- The orbit product stays in every subgroup containing its factors. -/
public theorem orbitProduct_mem (σ : G →* G) (m : ℕ) (x : G) (U : Subgroup G)
    (hmem : ∀ i < m, (σ^[i]) x ∈ U) : orbitProduct σ m x ∈ U := by
  apply U.list_prod_mem
  intro y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  exact hmem i i.isLt

/-- Unique ordered coordinates prevent a nonidentity first coordinate from
being lost in the orbit product. In applications each orbit label occurs once. -/
public theorem orbitProduct_ne_one (σ : G →* G) (m : ℕ) (hm : 0 < m)
    (Y : Fin m → Subgroup G)
    (hinj : Function.Injective (Subgroup.orderedProduct Y))
    (x : G) (hmem : ∀ i : Fin m, (σ^[i.val]) x ∈ Y i) (hne : x ≠ 1) :
    orbitProduct σ m x ≠ 1 := by
  intro heq
  let a : ∀ i, Y i := fun i => ⟨(σ^[i.val]) x, hmem i⟩
  have hprod : Subgroup.orderedProduct Y a =
      Subgroup.orderedProduct Y (fun _ => 1) := by
    simpa [Subgroup.orderedProduct, orbitProduct, a] using heq
  have ha := congrArg (fun f : ∀ i, Y i => ((f ⟨0, hm⟩ : Y ⟨0, hm⟩) : G))
    (hinj hprod)
  exact hne ha

end Theory.AlgebraicGroup.ProperParabolicFixedRadical
