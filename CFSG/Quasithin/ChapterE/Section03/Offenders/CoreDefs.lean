module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic

/-!
# The dual generated core

E.3.30 generates a subgroup from actual centralizers for a group action.
For the internal module we use the inclusion of the induced automizer into
`Aut(V)` and then map its fixed subgroups back into the ambient group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.30,
printed p. 237. The formula also makes sense at `k = 0`, which is needed
when E.3.31 uses `m(Ā) - 1` for an automizer of rank one.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {P H : Type*} [Group P] [Group H]

/-- The centralizer `C_H(X)` for the specified action by automorphisms. -/
def actionCentralizer (ρ : P →* MulAut H) (X : Subgroup P) : Subgroup H where
  carrier := {h | ∀ x ∈ X, ρ x h = h}
  one_mem' := by intro x _; exact map_one (ρ x)
  mul_mem' := by intro a b ha hb x hx; rw [map_mul, ha x hx, hb x hx]
  inv_mem' := by intro a ha x hx; rw [map_inv, ha x hx]

/-- E.3.30: generate by centralizers of actor subgroups of quotient rank at most `k`.
The intended actors are elementary abelian two-groups. -/
noncomputable def dualGeneratedCore (ρ : P →* MulAut H) (k : ℕ) : Subgroup H :=
  ⨆ (X : Subgroup P) (_ : Nat.log 2 X.index ≤ k), actionCentralizer ρ X

theorem actionCentralizer_le_dualGeneratedCore (ρ : P →* MulAut H)
    {k : ℕ} {X : Subgroup P} (hX : Nat.log 2 X.index ≤ k) :
    actionCentralizer ρ X ≤ dualGeneratedCore ρ k :=
  le_iSup_of_le X (le_iSup_of_le hX le_rfl)

theorem dualGeneratedCore_le (ρ : P →* MulAut H) {k : ℕ} {K : Subgroup H}
    (h : ∀ X : Subgroup P, Nat.log 2 X.index ≤ k → actionCentralizer ρ X ≤ K) :
    dualGeneratedCore ρ k ≤ K := by
  exact iSup_le fun X => iSup_le (h X)

variable {G : Type*} [Group G]

/-- The dual core in `V` for the actual automizer subgroup `I ≤ Aut_G(V)`,
regarded as a subgroup of the ambient group. -/
noncomputable def automizerDualCore (V : Subgroup G) (I : Subgroup (Automizer V))
    (k : ℕ) : Subgroup G :=
  (dualGeneratedCore ((Automizer V).subtype.comp I.subtype) k).map V.subtype

theorem automizerDualCore_le (V : Subgroup G) (I : Subgroup (Automizer V)) (k : ℕ) :
    automizerDualCore V I k ≤ V := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

end CFSG.Quasithin.ChapterE
