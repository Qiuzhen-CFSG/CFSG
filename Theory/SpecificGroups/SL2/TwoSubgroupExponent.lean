module

public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Exponent of two-subgroups in binary SL₂

Sylow conjugacy identifies every Sylow two-subgroup with the upper
unipotent group, which is the additive group of the field. Restriction
therefore makes every element of a two-subgroup square to one.

Source: GLS, volume 4, Chapter 4, Lemma 3.5(a), in the linear case.
-/

namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every two-subgroup of SL₂ over a finite field of characteristic two has exponent at most two. -/
public theorem twoSubgroup_pow_two (P : Subgroup (SpecialLinearGroup (Fin 2) F))
    (hP : IsPGroup 2 P) (x : P) : x ^ 2 = 1 := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  let e : Q ≃* Multiplicative F :=
    (Q.equiv (upperUnipotentSylow F 2)).trans
      (MonoidHom.ofInjective (upperUnipotentHom_injective F)).symm
  have hs (a : Multiplicative F) : a ^ 2 = 1 := by
    rw [pow_two]
    change Multiplicative.ofAdd (a.toAdd + a.toAdd) = Multiplicative.ofAdd 0
    rw [CharTwo.add_self_eq_zero]
  have hx : (⟨x, hPQ x.property⟩ : Q) ^ 2 = 1 := by
    apply e.injective
    simpa only [map_pow, map_one] using hs (e ⟨x, hPQ x.property⟩)
  exact Subtype.ext (congrArg (fun q : Q => (q : SpecialLinearGroup (Fin 2) F)) hx)

end Matrix.SpecialLinearGroup
