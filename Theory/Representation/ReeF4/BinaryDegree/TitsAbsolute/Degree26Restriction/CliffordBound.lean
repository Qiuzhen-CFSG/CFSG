module

public import Theory.Representation.Clifford
public import Theory.Representation.NormalInvariants
public import Theory.Representation.Quotient
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Restriction bounds from a large constituent

An irreducible constituent on a normal subgroup that has more than half the
ambient dimension is the whole restriction. Distinct conjugates are disjoint,
contradicting the dimension bound; Clifford's conjugate-span lemma then gives
that the unique conjugate is the whole space.

Over an algebraically closed field, a nonzero commutator-fixed vector in an
irreducible representation forces degree one, by descent to the abelianization.
Consequently, when the commutator subgroup is simple and the degree is not one,
every nonzero subrepresentation of the restriction is faithful. Together these
facts reduce irreducibility of restriction to a faithful-degree lower bound.

Source: the normal-subgroup argument of Clifford theory, as in Isaacs,
*Character Theory of Finite Groups*, Theorem 6.5. These lemmas also hold in
modular characteristic; no semisimplicity of the group algebra is assumed.
-/

public section

open Representation
namespace Representation
variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A constituent occupying more than half the space forces irreducibility
on a normal subgroup: two distinct conjugates would be disjoint. -/
theorem irreducible_restrict_of_large_constituent
    (ρ : Representation F G V) (H : Subgroup G) [H.Normal]
    (hρ : ρ.IsIrreducible) (W : Subrepresentation (ρ.comp H.subtype))
    (hW : W.toRepresentation.IsIrreducible)
    (hdim : Module.finrank F V < 2 * Module.finrank F W.toSubmodule) :
    Representation.IsIrreducible (ρ.comp H.subtype) := by
  have ha : IsAtom W := (Subrepresentation.irreducible_iff_isAtom W).mp hW
  have heq (g : G) : conjugateSubrepresentation ρ H W g = W := by
    let U := conjugateSubrepresentation ρ H W g
    have hUa : IsAtom U := by
      have h := (conjugateSubrepresentationOrderIso ρ H g⁻¹).isAtom_iff W
      simpa using h.mpr ha
    have hUd : Module.finrank F U.toSubmodule = Module.finrank F W.toSubmodule := by
      exact (conjugateSubrepresentationEquiv ρ H W g).toLinearEquiv.finrank_eq
    by_contra hne
    have hdis : Disjoint U.toSubmodule W.toSubmodule := by
      rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (hUa.disjoint_of_ne ha hne).eq_bot
    have hle := Submodule.finrank_add_finrank_le_of_disjoint hdis
    rw [hUd] at hle
    omega
  have hspan := iSup_conjugateSubrepresentations_eq_top ρ H hρ W hW
  simp only [heq, iSup_const] at hspan
  exact isSimpleOrder_iff_isAtom_top.mpr (hspan ▸ ha)

/-- An irreducible representation with a commutator-fixed vector has degree one
when its field is algebraically closed. -/
theorem finrank_eq_one_of_derived_invariants_ne_bot [IsAlgClosed F]
    (ρ : Representation F G V) [ρ.IsIrreducible]
    (hfix : invariants (ρ.comp (commutator G).subtype) ≠ ⊥) :
    Module.finrank F V = 1 := by
  have hker := le_ker_of_normal_invariants_ne_bot ρ (commutator G) hfix
  let σ : Representation F (Abelianization G) V :=
    quotientOfLEKer ρ (commutator G) hker
  let : σ.IsIrreducible :=
    (quotientOfLEKer_irreducible_iff ρ (commutator G) hker).mpr inferInstance
  exact IsIrreducible.finrank_eq_one_of_isMulCommutative σ

/-- If the derived subgroup is simple, every nonzero constituent of an
irreducible representation of degree other than one is faithful on it. -/
theorem faithful_derived_constituent [IsAlgClosed F] [IsSimpleGroup (commutator G)]
    (ρ : Representation F G V) [ρ.IsIrreducible]
    (hdim : Module.finrank F V ≠ 1)
    (W : Subrepresentation (ρ.comp (commutator G).subtype)) (hW : W ≠ ⊥) :
    Function.Injective W.toRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff W.toRepresentation).mp
  apply (Subgroup.Normal.eq_bot_or_eq_top (inferInstance : W.toRepresentation.ker.Normal)).resolve_right
  intro hker
  apply hdim
  apply finrank_eq_one_of_derived_invariants_ne_bot ρ
  have hle : W.toSubmodule ≤ invariants (ρ.comp (commutator G).subtype) := by
    intro v hv g
    have hg : W.toRepresentation g = 1 :=
      MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g)
    exact congrArg Subtype.val (DFunLike.congr_fun hg (⟨v, hv⟩ : W))
  intro hbot
  apply hW
  apply Subrepresentation.toSubmodule_injective
  exact le_bot_iff.mp (hle.trans_eq hbot)

end Representation
