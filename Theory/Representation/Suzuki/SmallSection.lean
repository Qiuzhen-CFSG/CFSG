module
public import Theory.Representation.Suzuki.SmallDegree
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Natural subquotients of small binary Suzuki actions

A nontrivial binary action of Sz(2^(2m+1)), m > 0, on a space of dimension
less than 10(2m+1) has an actual invariant subquotient isomorphic to the
natural module. Perfectness makes a nontrivial action survive on a simple
section; simplicity makes that section faithful; the existing small-degree
classification identifies it. The action on the original module need not
be irreducible or semisimple.

This is used on the literal radical Frattini quotient in Fong--Seitz I
(6C), printed p.40. The representation classification is the one assembled
in Suzuki/SmallDegree from Guralnick--Malle, Classification of 2F-modules II,
§3.1 and §8, and Aschbacher--Smith K.3, printed p.457.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative

/-- A nontrivial small binary action contains the natural module as an actual
invariant subquotient. No irreducibility of the original action is assumed. -/
theorem exists_natural_section {m : ℕ} (hm : 0 < m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hne : ρ ≠ 1)
    (hsmall : Module.finrank (ZMod 2) V < 10*(2*m+1)) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
      Nonempty (N.quotientRepresentation.Equiv (SuzukiNatural.natural m)) := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsPerfect (SuzukiMatrixGroup m) := ⟨by
    rcases (inferInstance : (commutator (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top
      with hb | ht
    · let : IsMulCommutative (SuzukiMatrixGroup m) := (commutator_eq_bot_iff _).mp hb
      exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm inferInstance).elim
    · exact ht⟩
  have hn : ¬ (⊤ : Subgroup (SuzukiMatrixGroup m)) ≤ ρ.ker := by
    intro hh
    exact hne (MonoidHom.ker_eq_top_iff.mp (top_unique hh))
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup (SuzukiMatrixGroup m)) hn
  have hf : Function.Injective N.quotientRepresentation := by
    apply N.quotientRepresentation.ker_eq_bot_iff.mp
    exact (inferInstance : N.quotientRepresentation.ker.Normal).eq_bot_or_eq_top.resolve_right
      (fun he => hn he.ge)
  have hd : Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) < 10*(2*m+1) :=
    ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le U.toSubmodule)).trans_lt hsmall
  exact ⟨U,N,hi,natural_equiv_of_smallDegree (by omega) _ hf hi hd⟩

end Representation.SuzukiSmallDegree
