module

public import Theory.Representation.HexacodeAction.FullWeightFourVectorStabilizer

/-!
# A nonzero Sylow-fixed hexacode vector has weight four

The full group and its even subgroup have the same nonzero vector orbits.
A weight-six vector has stabilizer of order120, which cannot contain the
literal Sylow group of order16. The retained vector therefore has weight
four, and its full stabilizer has the established marked S2 times S4 model.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode

theorem weight_four_of_sylow_fixed (S : Sylow 2 HexAutomorphisms)
    (v : hexacode) (hv : v≠0) (hf : ∀ g : S, action g v=v) :
    hammingNorm v.val=4 := by
  let : MulAction HexAutomorphisms hexacode := {
    smul := fun g w => action g w
    one_smul := fun w => by change action 1 w=w; rw [map_one]; rfl
    mul_smul := fun g h w => by
      change action (g*h) w=action g (action h w)
      rw [map_mul,Module.End.mul_apply] }
  have ho : MulAction.orbit HexAutomorphisms v=
      Set.range (fun g : HexEvenAutomorphisms => evenAction g v) := by
    ext w
    constructor
    · rintro ⟨g,rfl⟩
      rw [evenAction_orbit_eq_weight v hv]
      exact Monomial.act_weight g.val v.val
    · rintro ⟨g,rfl⟩
      exact ⟨g.val,rfl⟩
  by_contra h4
  have hi : (fullVectorStabilizer v).index=18 := by
    change (MulAction.stabilizer HexAutomorphisms v).index=18
    rw [MulAction.index_stabilizer HexAutomorphisms v,ho,evenAction_orbit_card v hv]
    simp [h4]
  have hc : Nat.card (fullVectorStabilizer v)=120 := by
    have hh := (fullVectorStabilizer v).card_mul_index
    rw [hi,hexAutomorphisms_card] at hh
    omega
  have hS : Nat.card S=16 := by
    rw [S.card_eq_multiplicity,hexAutomorphisms_card]
    decide +kernel
  have hle : (S : Subgroup HexAutomorphisms)≤fullVectorStabilizer v :=
    fun g hg => hf ⟨g,hg⟩
  have hh := card_dvd_of_le hle
  rw [hS,hc] at hh
  norm_num at hh

end Representation.Hexacode
