module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Nonsolvability of the surviving F.6.18 source rows

After excluding the first two alternatives, each source row contains a
nontrivial perfect subgroup. In the product row this is the explicitly
embedded PSL₂ over its stated prime field. In the other rows it is the
quasisimple generalized Fitting subgroup. Both additional rank-one source
alternatives are retained.

The original HS amalgam consumes this result after excluding rows (1)--(2)
with its actual characteristic-two actor and distinct local cores.
Source: Aschbacher--Smith F.6.18, printed pp.309--310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {D : Type u} [Group D] [Finite D]
omit [Finite D] in
private theorem quasisimple_nonsolvable (h : IsQuasisimple D) : ¬ Group.IsSolvable D := by
  let : IsQuasisimple D := h
  let : IsSimpleGroup (D ⧸ center D) := h.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D

omit [Finite D] in
private theorem product_nonsolvable {S : Sylow 2 D} (r : ProductRow S) : ¬ Group.IsSolvable D := by
  intro hs
  let := hs
  have hlarge : 3 < Nat.card r.field.Carrier := by
    rw [r.field.card,r.degree,pow_one]
    have := r.congruence
    omega
  let : Group.IsPerfect PSL(2,r.field.Carrier) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three r.field.Carrier hlarge
  let : IsSimpleGroup PSL(2,r.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  exact Group.IsPerfect.not_isSolvable PSL(2,r.field.Carrier)
    (Group.isSolvable_of_surjective (f := r.firstEquiv.toMonoidHom) r.firstEquiv.surjective)

omit [Finite D] in
/-- Every remaining corrected source row is nonsolvable. -/
theorem source_alternative_nonsolvable
    {A B : Subgroup D} {S : Sylow 2 D} (h : SourceAlternative A B S)
    (h1 : ¬ Nonempty (S ≃* C 2))
    (h2 : ¬ (Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* E4))) : ¬ Group.IsSolvable D := by
  rcases h with (h | ⟨r⟩) | ⟨r⟩
  · cases h with
    | one h _ _ _ => exact (h1 h).elim
    | two h => exact (h2 h).elim
    | three r _ _ _ => exact product_nonsolvable r
    | four _ _ _ _ _ h _ _ _
    | five _ _ _ _ _ h _ _ _
    | six _ _ h _ _ _
    | seven _ h _ _ _
    | eight _ h _ _ _
    | nine _ h _ _ _
    | ten _ _ _ _ _ h _ _ _
    | eleven _ h _ _ _
    | twelve _ h _ _ _
    | thirteen _ _ h _ _ _ =>
      intro hs
      let := hs
      exact quasisimple_nonsolvable h inferInstance
  · intro hs
    let := hs
    exact quasisimple_nonsolvable r.some.quasisimple inferInstance
  · intro hs
    let := hs
    exact quasisimple_nonsolvable r.some.quasisimple inferInstance
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
