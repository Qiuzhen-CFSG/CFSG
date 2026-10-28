module

public import Theory.Representation.PSL3Two.ResidualFFForms.Criteria
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.DualBounds
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The simple-constituent dual budget for binary SL₃(2)

Every nontrivial irreducible representation affordable for a nontrivial
elementary two-subgroup is natural or dual-natural. Three conjugate
involutions give dimension at most six, excluding the eight-dimensional
Steinberg alternative in the actual irreducible catalogue. The natural and
dual-natural representations are inequivalent, and their combined fixed
codimension exceeds the rank of the same acting subgroup.

The result is the concrete constituent input to the invariant-form argument
of Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.4) and (3.8), printed pp.842 and 878. The four-model catalogue
is Aschbacher–Smith H.6.1, printed p.386 of the combined manuscript of
1 March 2004. All comparisons below are actual representation equivalences
for the same group; no semisimplicity or faithfulness assumption is used.
-/

public section

open Representation Representation.BinaryOffender

namespace BinaryLinearThree.ResidualFFForms

universe u

private theorem fixedCodim_equiv {G V X : Type*} [_root_.Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) G V} {τ : Representation (ZMod 2) G X}
    (e : σ.Equiv τ) (A : Subgroup G) : fixedCodim σ A = fixedCodim τ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant σ τ (MonoidHom.id G)
    e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

-- Pullback along the inverse linear equivalence intertwines contragredients.
private def dualEquiv {G V X : Type*} [_root_.Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) G V} {τ : Representation (ZMod 2) G X}
    (e : σ.Equiv τ) : σ.dual.Equiv τ.dual :=
  .mk e.symm.toLinearEquiv.dualMap (by
    intro g
    ext f w
    exact congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' g⁻¹) w).symm)

private noncomputable def doubleDualEquiv {G V : Type*} [_root_.Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) G V) : σ.Equiv σ.dual.dual :=
  .mk (Module.evalEquiv (ZMod 2) V) (by
    intro g
    ext v f
    change f (σ g v) = f (σ (g⁻¹)⁻¹ v)
    rw [inv_inv])

/-- The literal binary SL₃(2) satisfies the simple-constituent budget at
every nontrivial elementary abelian two-subgroup, in every module universe. -/
theorem simpleBudget (A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hne : A ≠ ⊥) (hA : IsElementaryAbelian 2 A) :
    SimpleBudget.{u} A (rank A) := by
  intro V _ _ _ σ hi hn hb
  let : IsIrreducible σ := hi
  have hd : Module.finrank (ZMod 2) V ≤ 6 :=
    ConstituentBudget.finrank_le_six_of_irreducible σ hn ⟨A, ⟨hne, hA⟩, hb⟩
  have hmove : ∃ g : Group, ∃ v : V, σ g v ≠ v := by
    by_contra! h
    apply hn
    ext g v
    exact h g v
  have hsum := ConstituentBudget.rank_lt_natural_add_dual_fixedCodim A ⟨hne, hA⟩
  rcases IrreducibleCatalogue.classify_nontrivial σ hmove with h | h | h
  · obtain ⟨e⟩ := h
    constructor
    · rintro ⟨f⟩
      exact AutomorphismAction.natural_not_equiv_dual
        ⟨e.symm.trans (f.trans (dualEquiv e))⟩
    · rw [fixedCodim_equiv e, fixedCodim_equiv (dualEquiv e)]
      exact hsum
  · obtain ⟨e⟩ := h
    let e' : σ.dual.Equiv W := (dualEquiv e).trans (doubleDualEquiv W).symm
    constructor
    · rintro ⟨f⟩
      exact AutomorphismAction.natural_not_equiv_dual
        ⟨e'.symm.trans (f.symm.trans e)⟩
    · rw [fixedCodim_equiv e, fixedCodim_equiv e', Nat.add_comm]
      exact hsum
  · obtain ⟨e⟩ := h
    have he := e.toLinearEquiv.finrank_eq
    rw [finrank_steinberg] at he
    omega

end BinaryLinearThree.ResidualFFForms
