module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Model

/-!
# One marking for the orthogonal section and the original seed

When the moved-section coordinates extend to the original seed span with
the same actor, rotate both by the permutation supplied by the Sylow-fixed
seed argument. The resulting moved-section coordinates remain equivariant
and mark the literal seed stabilizer and centralizer. This is the assembly
step shared by the terminal local-action and Thompson consumers.

The two coordinate constructions are still explicit premises here; their
existence must be established from the full source FF alternatives.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph following 13.6.23, printed p.933 (PDF p.950).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
open ComponentSelection Theory.SpecificGroups.SymmetricEight
variable {G : Type*} [Group G] [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- A single choice marks the original seed and the orthogonal moved section.
The rotation preserves the upper and central subrepresentations definitionally. -/
theorem exists_compatible_marking
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (d : NaturalMovedSection K L T z v hL hz)
    (s : NaturalSeedSection K L T z v hL hz) (ha : d.actor = s.actor) :
    ∃ r : Equiv.Perm (Fin 8),
      (seedStabilizer K L T z v hL hz).map
        (d.conjugate K L T z v hL hz r).actor.toMonoidHom =
          A6ShadowTwoLocals.fourStabilizer ∧
      (plusImage K L T z v hL hz (K ⊓ Gv z)).map
        (d.conjugate K L T z v hL hz r).actor.toMonoidHom =
          alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer ∧
      (((plusImage K L T z v hL hz (K ⊓ Gv z)).map
        (d.conjugate K L T z v hL hz r).actor.toMonoidHom).subgroupOf
          (alternatingGroup (Fin 8))).map FourBlockParabolic.equiv.toMonoidHom =
            BinaryLinear.parabolic FourBlockParabolic.plane := by
  obtain ⟨r, s', hs', hseed, hcent, hpar⟩ :=
    exists_marked_centralizer K L T z v hL hz hY hK hLK hSyl s
  have he : (d.conjugate K L T z v hL hz r).actor = s'.actor := by
    rw [hs']
    exact congrArg (fun e => e.trans (MulAut.conj r)) ha
  exact ⟨r, he.symm ▸ hseed, he.symm ▸ hcent, he.symm ▸ hpar⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
