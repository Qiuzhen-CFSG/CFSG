module

public import Theory.SpecificGroups.AlternatingSevenNotMinimal
public import Stellmacher.Recognition.DihedralSimple
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# The dihedral Sylow branch for minimal simple groups

The Gorenstein--Walter simple-group conclusion has two alternatives: A7 and
PSL2 over an odd finite field. Minimal simplicity excludes A7, since its
natural A5 subgroup is nonsolvable and proper. Nonsolvability of the remaining
PSL2 model excludes fields of cardinality at most three.

The second theorem applies this refinement to any supplied dihedral Sylow
two-subgroup. Both conclusions give actual group isomorphisms. The sharper
prime and prime-exponent restrictions of Thompson's final list remain separate
from this recognition theorem.

Source: the simple-group corollary of Gorenstein--Walter as exported by
Stellmacher.Recognition.DihedralSimple, and the natural A5 inclusion in A7.
-/

namespace Stellmacher.Recognition

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Refine the Gorenstein--Walter alternatives using minimal simplicity. -/
public theorem minimalSimple_gorensteinWalter_recognition (hG : IsMinimalSimple G)
    (hmodel : Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type u) (instK : Field K) (_ : Finite K),
        let : Field K := instK
        Odd (Nat.card K) ∧ Nonempty (G ≃* GorensteinWalter.PSL2 K)) :
    ∃ (K : Type u) (instK : Field K) (_ : Finite K),
      let : Field K := instK
      Odd (Nat.card K) ∧ 3 < Nat.card K ∧
        Nonempty (G ≃* GorensteinWalter.PSL2 K) := by
  rcases hmodel with hA | hPSL
  · obtain ⟨e⟩ := hA
    exact (alternatingGroup.not_isMinimalSimple_seven (hG.of_mulEquiv e)).elim
  · obtain ⟨K, hK, hfinite, hodd, ⟨e⟩⟩ := hPSL
    let _ := hK
    let _ := hfinite
    refine ⟨K, hK, hfinite, hodd, ?_, ⟨e⟩⟩
    apply Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable hodd
    intro hsolv
    let _ := hsolv
    exact hG.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- A minimal simple group with dihedral Sylow two is an actual odd-field PSL2. -/
public theorem minimalSimple_dihedral_recognition (hG : IsMinimalSimple G)
    (S : Sylow 2 G) (hS : IsDihedralGroup S) :
    ∃ (K : Type u) (instK : Field K) (_ : Finite K),
      let : Field K := instK
      Odd (Nat.card K) ∧ 3 < Nat.card K ∧
        Nonempty (G ≃* GorensteinWalter.PSL2 K) := by
  let _ := hG.isSimpleGroup
  exact minimalSimple_gorensteinWalter_recognition hG
    (simple_dihedral_recognition hG.not_isSolvable S hS)

end Stellmacher.Recognition
