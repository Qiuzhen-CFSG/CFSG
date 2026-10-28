module
public import Theory.GroupAction.Lemmas

/-!
# Displacement across three supports

Suppose an automorphism moves a subgroup `U` onto `W` and then `W` onto
`T`, with `U` disjoint from `W ⊔ T` and `W` disjoint from `T`. Its
displacement on `U * W` is injective: a fixed product `u * w` forces
`u` into `U ∩ (W ⊔ T)`, and then `w` into `W ∩ T`.

This is the support-counting step in Aschbacher--Smith, *The Classification
of Quasithin Groups*, D.2.12, printed p.184.
-/

open scoped IsMulCommutative

universe u v

/-- Three successive independent supports contribute the product of their
first two orders to the action commutator subgroup. -/
public theorem commutatorAction_card_ge_mul_of_three_supports
    {A : Type u} {V : Type v} [Group A] [Group V] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction A V]
    (S : Subgroup A) (c : A) (hc : c ∈ S)
    (U W T : Subgroup V)
    (hUW : U.map (MulDistribMulAction.toMulAut A V c).toMonoidHom = W)
    (hWT : W.map (MulDistribMulAction.toMulAut A V c).toMonoidHom = T)
    (hU : Disjoint U (W ⊔ T)) (hW : Disjoint W T) :
    Nat.card U * Nat.card W ≤ Nat.card (commutatorAction S V) := by
  let delta : U × W →* V :=
    { toFun := fun p => ((p.1 : V) * (p.2 : V))⁻¹ * (c • ((p.1 : V) * (p.2 : V)))
      map_one' := by simp
      map_mul' := by
        intro p q
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, smul_mul', mul_inv_rev]
        ac_rfl }
  have hker (p : U × W) (hp : delta p = 1) : p = 1 := by
    have hfixed : (p.1 : V) * (p.2 : V) = (c • (p.1 : V)) * (c • (p.2 : V)) := by
      have hh : ((p.1 : V) * (p.2 : V))⁻¹ *
          ((c • (p.1 : V)) * (c • (p.2 : V))) = 1 := by
        simpa only [delta, MonoidHom.coe_mk, OneHom.coe_mk, smul_mul'] using hp
      exact inv_mul_eq_one.mp hh
    have hcu : c • (p.1 : V) ∈ W := by
      have hm : c • (p.1 : V) ∈
          U.map (MulDistribMulAction.toMulAut A V c).toMonoidHom := by
        exact Subgroup.mem_map_of_mem
          (MulDistribMulAction.toMulAut A V c).toMonoidHom p.1.property
      exact (congrArg (fun H : Subgroup V => c • (p.1 : V) ∈ H) hUW).mp hm
    have hcw : c • (p.2 : V) ∈ T := by
      have hm : c • (p.2 : V) ∈
          W.map (MulDistribMulAction.toMulAut A V c).toMonoidHom := by
        exact Subgroup.mem_map_of_mem
          (MulDistribMulAction.toMulAut A V c).toMonoidHom p.2.property
      exact (congrArg (fun H : Subgroup V => c • (p.2 : V) ∈ H) hWT).mp hm
    have huJoin : (p.1 : V) ∈ W ⊔ T := by
      have hright : (c • (p.1 : V)) * (c • (p.2 : V)) * (p.2 : V)⁻¹ ∈ W ⊔ T := by
        exact (W ⊔ T).mul_mem
          ((W ⊔ T).mul_mem ((le_sup_left : W ≤ W ⊔ T) hcu)
            ((le_sup_right : T ≤ W ⊔ T) hcw))
          ((le_sup_left : W ≤ W ⊔ T) (W.inv_mem p.2.property))
      convert hright using 1
      rw [← hfixed]
      group
    have hu : p.1 = 1 := Subtype.ext (hU.le_bot ⟨p.1.property, huJoin⟩)
    have hwT : (p.2 : V) ∈ T := by
      have hfixW : (p.2 : V) = c • (p.2 : V) := by
        simpa only [hu, Subgroup.coe_one, one_mul, smul_one] using hfixed
      rw [hfixW]
      exact hcw
    have hw : p.2 = 1 := Subtype.ext (hW.le_bot ⟨p.2.property, hwT⟩)
    exact Prod.ext hu hw
  have hinjective : Function.Injective delta :=
    (injective_iff_map_eq_one delta).mpr hker
  have hcard : Nat.card delta.range = Nat.card U * Nat.card W := by
    change Nat.card (Set.range delta) = _
    rw [(Nat.card_congr (Equiv.ofInjective delta hinjective)).symm, Nat.card_prod]
  have hfull : delta.range ≤ commutatorAction S V := by
    rintro point ⟨preimage, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨c, hc⟩,
      (preimage.1 : V) * (preimage.2 : V), rfl⟩
  exact hcard ▸ Subgroup.card_le_of_le hfull
