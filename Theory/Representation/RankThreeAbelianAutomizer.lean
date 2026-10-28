module

public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.ExtendScalars
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.PGroup

/-!
# Abelian cross-characteristic matrix automizers

An abelian subgroup of `GL(n,F)` whose order is nonzero in `F` has its induced
automizer embedded in `S_n`. Extend the faithful natural representation to the
algebraic closure: faithfulness and dimension are preserved. The normalizer
permutes the nonzero simultaneous character weight spaces; there are at most
`n` of them, and the kernel of that action is exactly the centralizer.

The degree-three specialization proves the abelian branch of Aschbacher–Smith,
Lemma A.3.21(c), refs/quasithin.pdf, printed pp. 55–56 (PDF pp. 66–67).
For a `q`-group in characteristic `p ≠ q`, its order is nonzero in the field.
Oddness of `q` is not needed in this branch, and the trivial subgroup is included.
-/

public section

namespace Representation

variable {F : Type*} [Field F]

/-- Over any field, a cross-characteristic abelian matrix subgroup has automizer
embedding in the symmetric group of its degree. -/
theorem generalLinear_abelian_automizer_embeds_perm (n : ℕ) (Q : Subgroup (GL (Fin n) F))
    [IsMulCommutative Q] (horder : (Nat.card Q : F) ≠ 0) :
    ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm (Fin n), Function.Injective j := by
  let E := AlgebraicClosure F
  let rho := (generalLinearNatural (F := F) n).extendScalars E
  have hrho : Function.Injective rho :=
    (extendScalars_faithful_iff E _).mp (generalLinearNatural_injective n)
  have horder' : (Nat.card Q : E) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap F E).injective
    simpa using h
  apply automizer_embeds_perm_of_abelian rho Q hrho horder' n
  simp only [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_fin, le_refl]

/-- The abelian branch of A.3.21(c). Oddness of `q` is unnecessary for this branch. -/
theorem rankThree_abelian_automizer_embeds_perm [Finite F]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [CharP F p]
    (hpq : q ≠ p) (Q : Subgroup (GL (Fin 3) F))
    (hQ : IsPGroup q Q) [IsMulCommutative Q] :
    ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm (Fin 3), Function.Injective j := by
  apply generalLinear_abelian_automizer_embeds_perm 3 Q
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  rw [ha, Nat.cast_pow]
  apply pow_ne_zero
  rw [Ne, CharP.cast_eq_zero_iff]
  exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
    (Fact.out : q.Prime)).mp h).symm

end Representation
