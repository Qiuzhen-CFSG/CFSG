module
public import Theory.Representation.BinaryPermutation.SixTransitivity
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.SpecificGroups.AlternatingSix.CubicPreimageRank
public import Mathlib.GroupTheory.Index

/-!
# Natural A₆ point stabilizers under a cubic central cover

Transitivity on the fifteen nonzero vectors gives point stabilizer order 24.
The inverse image of a cubic in this stabilizer is elementary abelian of
order nine under a central cubic cover. Thus each nonzero point preimage
has three-rank at least two. The fixed-core consumer retains the two-group
kernel when transferring this rank to the ambient point centralizer.

Source: Aschbacher--Smith 13.4.10(3), printed p.908; the cover exponent
calculation is the proved GLS3 5.2.3 input of CubicPreimageRank.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryPermutation.SixNaturalCoverPoint
open BinaryNaturalDual.VectorStabilizers
abbrev Actor := alternatingGroup (Fin 6)
abbrev Space := natural (Fin 6)
abbrev action := alternatingNaturalRepresentation (Fin 6)
abbrev point (w : Space) := representationStabilizer action w

theorem point_card (w : Space) (hw : w ≠ 0) : Nat.card (point w) = 24 := by
  let : MulAction Actor Space := {
    smul := fun g v => action g v
    one_smul := fun v => by change action 1 v = v; simp
    mul_smul := fun g h v => by
      change action (g*h) v = action g (action h v)
      rw [map_mul,Module.End.mul_apply] }
  have horbit : MulAction.orbit Actor w = ({0} : Set Space)ᶜ := by
    ext v
    constructor
    · rintro ⟨g,rfl⟩
      change action g w ≠ 0
      intro he
      apply hw
      have hh := congrArg (action g⁻¹) he
      simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply,map_zero] using hh
    · intro hv
      exact alternatingSix_natural_nonzero_transitive w v hw hv
  have hcard : Nat.card Space = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      finrank_natural_even _ (by decide)]
    norm_num
  have hi : (point w).index = 15 := by
    change (MulAction.stabilizer Actor w).index = 15
    rw [MulAction.index_stabilizer,horbit,Set.ncard_compl,Set.ncard_singleton,hcard]
  have hh := (point w).card_mul_index
  have ha : Nat.card Actor = 360 := by rw [nat_card_alternatingGroup]; norm_num [Nat.card_fin,Nat.factorial]
  rw [hi,ha] at hh
  omega

theorem two_le_rank_preimage {E : Type*} [Group E] [Finite E]
    (q : E →* Actor) (hq : Function.Surjective q)
    (hc : q.ker ≤ center E) (hk : Nat.card q.ker = 3)
    (w : Space) (hw : w ≠ 0) :
    2 ≤ primeRank 3 ((point w).comap q) :=
  Theory.SpecificGroups.AlternatingSix.CubicPreimageRank.two_le_rank_preimage
    q hq hc hk (point w) (by rw [point_card w hw]; decide)
end BinaryPermutation.SixNaturalCoverPoint

