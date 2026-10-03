module
public import Theory.GroupTheory.PGroup.TrivialImage

/-!
# Nilpotent groups without normal subgroups of prime index

A finite nilpotent group without a normal subgroup of index p has order
prime to p. Project the finite nilpotent Sylow direct-product decomposition
onto a p-Sylow factor. The no-prime-index trivial-image theorem makes this
surjective homomorphism trivial, so the p-Sylow is trivial and p cannot
divide the group order.

This supplies the odd-order quotient step for the Sylow-intersection
comparison in Alperin–Brauer–Gorenstein II.3, Proposition 3 (pp.25–26),
without any campaign-specific hypotheses.
-/

/-- In a finite nilpotent group, every prime divisor of the order occurs as
an index of a normal subgroup. -/
public theorem Group.not_dvd_card_of_nilpotent_of_no_normal_index_prime
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime]
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ p) : ¬ p ∣ Nat.card G := by
  classical
  intro hdvd
  let ps := (Nat.card G).primeFactors
  let p' : ps := ⟨p, Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩⟩
  let P : Sylow p G := default
  obtain ⟨e⟩ := ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 4).mp
    (show Group.IsNilpotent G from inferInstance)
  let f : G →* P := ((Pi.evalMonoidHom (fun Q : Sylow p G => (Q : Subgroup G)) P).comp
    (Pi.evalMonoidHom (fun q : ps => ∀ Q : Sylow q G, (Q : Subgroup G)) p')).comp
      e.symm.toMonoidHom
  have hf : Function.Surjective f :=
    (Function.surjective_eval P).comp ((Function.surjective_eval p').comp e.symm.surjective)
  have hP : (P : Subgroup G) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    change x = 1
    obtain ⟨g, hg⟩ := hf ⟨x, hx⟩
    have he := MonoidHom.eq_one_of_no_normal_index_prime hno P.isPGroup' f g
    rw [hg] at he
    exact congrArg Subtype.val he
  have hi := P.not_dvd_index
  rw [hP, Subgroup.index_bot] at hi
  exact hi hdvd

