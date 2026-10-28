module

public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.NormalInvariants

/-!
# Orders of normal abelian subgroups in faithful irreducible representations

For a faithful irreducible representation of a finite group over any field,
the order of each normal abelian subgroup is nonzero in the coefficient field.
Finite dimension is a consequence of irreducibility and group finiteness,
not an additional hypothesis.

If the order vanished, the field characteristic would be a prime dividing
it. A Sylow subgroup for that prime is characteristic in the abelian subgroup
and hence normal in the ambient group. The modular fixed-vector theorem
`pGroup_fix_nonzero_vector` gives a nonzero fixed vector; normality and
irreducibility then put the whole Sylow subgroup in the representation kernel.
Faithfulness contradicts its nontriviality.

This supplies the nonmodular kernel-order reduction implicit in ABG II.8,
Lemma 4 (article p64, PDF p65), before decomposing the abelian kernel action.
The statement and proof do not require a Frobenius complement.
-/

namespace Representation

/-- A normal abelian subgroup has nonzero order in the coefficient field of
a faithful irreducible representation of a finite group. -/
public theorem card_normal_abelian_ne_zero_of_faithful_irreducible
    {F H V : Type*} [Field F] [Group H] [Finite H]
    [AddCommGroup V] [Module F V]
    (rho : Representation F H V) (K : Subgroup H)
    [K.Normal] [IsMulCommutative K] [IsIrreducible rho]
    (hfaithful : Function.Injective rho) : (Nat.card K : F) ≠ 0 := by
  intro hzero
  have hdiv : ringChar F ∣ Nat.card K :=
    (CharP.cast_eq_zero_iff F (ringChar F) _).mp hzero
  have hchar : ringChar F ≠ 0 := by
    intro heq
    rw [heq, zero_dvd_iff] at hdiv
    exact Nat.card_pos.ne' hdiv
  let : Fact (ringChar F).Prime := ringChar_prime hchar
  let sylow : Sylow (ringChar F) K := default
  let : (sylow : Subgroup K).Characteristic :=
    sylow.characteristic_of_normal inferInstance
  let normalSylow : Subgroup H := (sylow : Subgroup K).map K.subtype
  let : normalSylow.Normal := ConjAct.normal_of_characteristic_of_normal
  let : FiniteDimensional F V :=
    finiteDimensional_of_irreducible_finite_group rho inferInstance
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  obtain ⟨vector, hvector, hfixed⟩ := pGroup_fix_nonzero_vector hchar
    (sylow.isPGroup'.map K.subtype) (rho.comp normalSylow.subtype)
  have hfix : Representation.invariants (rho.comp normalSylow.subtype) ≠ ⊥ := by
    intro hbot
    have hmem : vector ∈ Representation.invariants (rho.comp normalSylow.subtype) := hfixed
    rw [hbot, Submodule.mem_bot] at hmem
    exact hvector hmem
  have hker := le_ker_of_normal_invariants_ne_bot rho normalSylow hfix
  have hbot : normalSylow = ⊥ := by
    apply le_antisymm _ bot_le
    intro element helement
    have heq := MonoidHom.mem_ker.mp (hker helement)
    exact Subgroup.mem_bot.mpr (hfaithful (heq.trans (map_one rho).symm))
  exact sylow.ne_bot_of_dvd_card hdiv
    ((Subgroup.map_eq_bot_iff_of_injective (sylow : Subgroup K)
      K.subtype_injective).mp hbot)

end Representation
