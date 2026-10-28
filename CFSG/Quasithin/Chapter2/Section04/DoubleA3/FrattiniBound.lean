module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.DihedralProduct
public import Theory.Frattini.PGroupMap

/-!
# Frattini bounds for the paired-cubic source subgroup

The source Frattini calculation identifies Φ(R) with the join of the two
marked fixed lines. Each line has order two, and the dihedral factor
coordinates make them disjoint and commuting. Thus |Φ(R)| = 4. Functoriality
of Frattini subgroups of finite two-groups transfers this bound to every
actual two-subgroup of R, including a component Sylow subgroup under its
original inclusion into G.

This supplies the Frattini bound in the symplectic component alternative
of Aschbacher–Smith 2.4.32, using the paired-cubic structure of 2.4.30,
printed pp.547–548.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)
include c

theorem thompson_frattini_card : Nat.card (frattini (sourceR d)) = 4 := by
  let I₁ := c.U₁ ⊓ centralizer (sourceR d : Set G)
  let I₂ := c.U₂ ⊓ centralizer (sourceR d : Set G)
  have hI₁ : I₁ ≤ c.U₁ ⊔ c.V₁ := inf_le_left.trans le_sup_left
  have hI₂ : I₂ ≤ c.U₂ ⊔ c.V₂ := inf_le_left.trans le_sup_left
  have hd : Disjoint I₁ I₂ := c.factor_product.1.mono hI₁ hI₂
  have hc : I₂ ≤ centralizer (I₁ : Set G) :=
    hI₂.trans ((le_centralizer_iff.mp c.factor_product.2.1).trans (centralizer_le hI₁))
  have hcard : Nat.card (I₁ ⊔ I₂ : Subgroup G) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint I₁ I₂
      (hc.trans (Subgroup.centralizer_le_normalizer _)) hd]
    change Nat.card (c.U₁ ⊓ centralizer (sourceR d : Set G) : Subgroup G) *
      Nat.card (c.U₂ ⊓ centralizer (sourceR d : Set G) : Subgroup G) = 4
    rw [c.first_fixed_line.1, c.second_fixed_line.1]
  calc
    Nat.card (frattini (sourceR d)) =
        Nat.card ((frattini (sourceR d)).map (sourceR d).subtype) :=
      (card_map_of_injective (sourceR d).subtype_injective).symm
    _ = 4 := by rw [c.frattini_eq_fixed_lines]; exact hcard

theorem subgroup_frattini_card_le (Q : Subgroup G) (hQR : Q ≤ sourceR d)
    (hQ : IsPGroup 2 Q) : Nat.card (frattini Q) ≤ 4 := by
  have hRS : sourceR d ≤ (d.S : Subgroup d.H).map d.H.subtype :=
    sSup_le (fun _ h => h.1)
  let : Fact (IsPGroup 2 (sourceR d)) :=
    ⟨(d.S.isPGroup'.map d.H.subtype).to_le hRS⟩
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hle := card_le_of_le
    (frattini_map_le_of_isPGroup (p := 2) (inclusion hQR))
  rw [card_map_of_injective (inclusion_injective hQR), c.thompson_frattini_card] at hle
  exact hle

end SourcePairCoordinates
end CFSG.Quasithin.Chapter2.DoubleA3
