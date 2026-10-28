module
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Solvable
public import Theory.Representation.BinaryPlaneBlocks

/-!
# The faithful pair action in the reducible G.10 branch

The original G.10 hypothesis makes every proper irreducible submodule a plane
in dimension four. Its trivial two-core then makes the two plane block actions
jointly faithful. Orbit generation also rules out a trivial actor. The final
applications retain the actual Chapter12 terminal quotient and representation.

Source: Aschbacher--Smith G.10.4--5, printed p.359.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The actual reducible group embeds in the two symmetric-three block actions. -/
theorem reducible_symmetricThree_pair (hred : ¬ Representation.IsIrreducible ρ) :
    ∃ f : G →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)), Function.Injective f := by
  let : Nontrivial V := ⟨⟨v,0,h.point_ne_zero⟩⟩
  obtain ⟨U,hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let : Representation.IsIrreducible U.toRepresentation := hU
  have hA := (Subrepresentation.irreducible_iff_isAtom U).mp hU
  have hU0 : U.toSubmodule ≠ ⊥ := fun he => hA.ne_bot (Subrepresentation.toSubmodule_injective he)
  have hUt : U.toSubmodule ≠ ⊤ := by
    intro he
    have he' : U=⊤ := Subrepresentation.toSubmodule_injective he
    exact hred (isSimpleOrder_iff_isAtom_top.mpr (he' ▸ hA))
  obtain ⟨hplane,hfour⟩ := h.proper_irreducible_submodule_degree U hU0 hUt
  have hquot : finrank (ZMod 2) (V ⧸ U.toSubmodule)=2 := by
    have he := U.toSubmodule.finrank_quotient_add_finrank
    omega
  exact ρ.exists_faithful_symmetricThree_pair_of_plane h.faithful U hplane hquot h.twoCore_eq_bot

/-- Orbit generation makes the acting group nontrivial in the reducible case. -/
theorem nontrivial_of_reducible (hred : ¬ Representation.IsIrreducible ρ) : Nontrivial G := by
  by_contra hn
  let : Subsingleton G := not_nontrivial_iff_subsingleton.mp hn
  have hs : Submodule.span (ZMod 2) {v}=⊤ := by
    apply top_unique
    rw [←h.orbit_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    have hg : ρ g v = v := by
      rw [Subsingleton.elim g (1:G), map_one]
      rfl
    rw [hg]
    exact (Submodule.mem_span_singleton_self v (R := ZMod 2))
  have hd := finrank_span_singleton (K := ZMod 2) h.point_ne_zero
  rw [hs,finrank_top,(h.reducible_degree_and_solvable hred).1] at hd
  omega
end CFSG.Quasithin.ChapterG.Section10.Hypothesis


namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The original terminal actor acts faithfully in the two symmetric-three blocks. -/
theorem terminal_reducible_symmetricThree_pair (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (h : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hred : ¬ Representation.IsIrreducible F.terminalRepresentation) :
    ∃ f : F.TerminalHdot →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      Function.Injective f :=
  h.reducible_symmetricThree_pair hred

/-- Orbit generation makes the actual reducible terminal actor nontrivial. -/
theorem terminal_nontrivial_of_reducible (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (h : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hred : ¬ Representation.IsIrreducible F.terminalRepresentation) :
    Nontrivial F.TerminalHdot :=
  h.nontrivial_of_reducible hred

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
