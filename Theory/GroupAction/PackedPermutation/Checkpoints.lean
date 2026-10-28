module
public import Theory.GroupAction.PackedPermutation.Soundness
/-!
# Relations and action tables from checked intermediate tables

Five passes through one network certify its fifth-power relation. Three
passes through two networks identify their product with a squared second
factor. Proving these statements before inserting the concrete masks keeps
algebraic transport independent of finite-table reduction cost.

The consumer is the pair of Bray words in the original Fi24 action.
-/
public section
namespace Theory.GroupAction.PackedPermutation

private theorem step_get (w n : Nat) (ss : List Stage)
    (hs : ∀ s∈ss, s.Valid w n) (u v : Nat) (h : run w ss u=v) (x : Fin n) :
    get w v x = get w u (permutation w n ss hs x) := by
  rw [← h]
  exact get_run w n u ss hs x

theorem fifth_power_of_checkpoints (w n : Nat) (ss : List Stage)
    (hs : ∀ s∈ss, s.Valid w n) (r t1 t2 t3 t4 : Nat)
    (hr : ∀ i : Fin n, get w r i=i.val)
    (h1 : run w ss r=t1) (h2 : run w ss t1=t2)
    (h3 : run w ss t2=t3) (h4 : run w ss t3=t4)
    (h5 : run w ss t4=r) : (permutation w n ss hs)^5=1 := by
  let p := permutation w n ss hs
  have e1 (x : Fin n) : get w t1 x=(p x).val :=
    (step_get w n ss hs r t1 h1 x).trans (hr (p x))
  have e2 (x : Fin n) : get w t2 x=(p (p x)).val :=
    (step_get w n ss hs t1 t2 h2 x).trans (e1 (p x))
  have e3 (x : Fin n) : get w t3 x=(p (p (p x))).val :=
    (step_get w n ss hs t2 t3 h3 x).trans (e2 (p x))
  have e4 (x : Fin n) : get w t4 x=(p (p (p (p x)))).val :=
    (step_get w n ss hs t3 t4 h4 x).trans (e3 (p x))
  apply Equiv.ext
  intro x
  apply Fin.ext
  have e5 := (step_get w n ss hs t4 r h5 x).trans (e4 (p x))
  rw [hr] at e5
  change ((p^5) x).val=x.val
  simpa only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using e5.symm

theorem product_square_of_checkpoints (w n : Nat) (ss ts : List Stage)
    (hs : ∀ s∈ss, s.Valid w n) (ht : ∀ s∈ts, s.Valid w n)
    (r u v z : Nat) (hr : ∀ i : Fin n, get w r i=i.val)
    (h1 : run w ss r=u) (h2 : run w ts u=v) (h3 : run w ts v=z)
    (x : Fin n) :
    get w z x = ((permutation w n ss hs * (permutation w n ts ht)^2) x).val := by
  let p := permutation w n ss hs
  let q := permutation w n ts ht
  have e1 (y : Fin n) : get w u y=(p y).val :=
    (step_get w n ss hs r u h1 y).trans (hr (p y))
  have e2 (y : Fin n) : get w v y=(p (q y)).val :=
    (step_get w n ts ht u v h2 y).trans (e1 (q y))
  have e3 := (step_get w n ts ht v z h3 x).trans (e2 (q x))
  change get w z x=((p*q^2) x).val
  simpa only [pow_two, Equiv.Perm.mul_apply] using e3

/-- Named permutations avoid unfolding concrete networks during action transport. -/
theorem product_square_of_named_checkpoints (w n : Nat) (ss ts : List Stage)
    (hs : ∀ s∈ss, s.Valid w n) (ht : ∀ s∈ts, s.Valid w n)
    (p q : Equiv.Perm (Fin n))
    (hp : permutation w n ss hs=p) (hq : permutation w n ts ht=q)
    (r u v z : Nat) (hr : ∀ i : Fin n, get w r i=i.val)
    (h1 : run w ss r=u) (h2 : run w ts u=v) (h3 : run w ts v=z)
    (x : Fin n) : get w z x=((p*q^2) x).val := by
  have H := product_square_of_checkpoints w n ss ts hs ht r u v z hr h1 h2 h3 x
  rw [hp,hq] at H
  exact H
end Theory.GroupAction.PackedPermutation
