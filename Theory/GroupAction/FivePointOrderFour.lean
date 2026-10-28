module
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic

/-!
# An order-four permutation cycles the four points outside its fixed point

On any finite set of five points, a permutation whose fourth power is one
and whose square is nonidentity acts transitively by its powers on the
complement of a supplied fixed point. The given permutation and points are
retained through a cardinality equivalence with Fin 5. A finite certificate
is checked by kernel reduction, then transported along that equivalence.

This elementary permutation fact supplies the final step in degree-five
local group actions, independently of any group classification or graph.
-/

namespace Equiv.Perm
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem five_certificate :
    ∀ p : Equiv.Perm (Fin 5), p^4=1 → p^2≠1 →
      ∀ root left right : Fin 5, p root=root → left≠root → right≠root →
        ∃ n : Fin 4, (p^n.val) left=right := by
  decide +kernel

public theorem exists_pow_apply_eq_of_order_four_card_five
    {X : Type*} [Finite X] (hX : Nat.card X=5)
    (p : Equiv.Perm X) (hfour : p^4=1) (hsquare : p^2≠1)
    {root left right : X} (hroot : p root=root)
    (hleft : left≠root) (hright : right≠root) :
    ∃ n : Fin 4, (p^n.val) left=right := by
  classical
  let e : X ≃ Fin 5 := (Finite.equivFin X).trans (finCongr hX)
  let q : Equiv.Perm (Fin 5) := Equiv.permCongr e p
  have hqfour : q^4=1 := by
    change (Equiv.permCongrHom e p)^4=1
    rw [←map_pow,hfour,map_one]
  have hqsquare : q^2≠1 := by
    intro heq
    apply hsquare
    apply (Equiv.permCongr e).injective
    change Equiv.permCongrHom e (p^2)=Equiv.permCongrHom e 1
    rw [map_pow,map_one]
    exact heq
  have hqroot : q (e root)=e root := by simp [q,Equiv.permCongr_apply,hroot]
  obtain ⟨n,hn⟩ := five_certificate q hqfour hqsquare (e root) (e left) (e right)
    hqroot (fun h => hleft (e.injective h)) (fun h => hright (e.injective h))
  refine ⟨n,e.injective ?_⟩
  have hp : q^n.val=Equiv.permCongr e (p^n.val) :=
    (map_pow (Equiv.permCongrHom e) p n.val).symm
  simpa only [hp,Equiv.permCongr_apply,Equiv.symm_apply_apply] using hn
end Equiv.Perm
