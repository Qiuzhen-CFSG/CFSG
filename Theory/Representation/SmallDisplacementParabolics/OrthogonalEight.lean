module

public import Theory.Representation.SmallDisplacementParabolics.Transport
public import Theory.Representation.BinaryPermutation.EightSylowFixed
public import Theory.SpecificGroups.SymmetricEight.CentralPair

/-!
# A moving parabolic in the six-dimensional binary S₈ module

The tree Sylow has order128 and lies in the four-pair stabilizer of order384.
Thus that stabilizer has no proper overgroup of the marked Sylow below it.
The nonzero Sylow-fixed vector has the four-block stabilizer, which does not
contain the permutation interchanging the pairs23 and45. The four-pair
subgroup therefore moves the vector, and its residual does too by the Sylow
supplement theorem. Sylow conjugacy and actual intertwining maps transfer
this calculation to every marking. No hypothesis on X or its two-core is
needed in this row.

Source: Aschbacher--Smith, original15.2.27(2), printed p.1119 (PDF p.1136).
The permutation argument uses the intrinsic eight-point module and does not
require the exceptional A₈--GL₄(2) comparison.
-/

public section
open Representation
namespace Representation.SmallDisplacementParabolics.OrthogonalEight
open Subgroup BinaryPermutation
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private theorem pair_card : Nat.card pairStabilizer = 384 := by
  rw [← Theory.SpecificGroups.SymmetricEight.CentralPair.centralizer_mate,
    Equiv.Perm.nat_card_centralizer]
  have hm : Theory.SpecificGroups.SymmetricEight.CentralPair.mate.cycleType = {2,2,2,2} := by
    decide +kernel
  rw [hm]
  norm_num [Nat.factorial]

private theorem tree_pair_index : treeGroup.relIndex pairStabilizer = 3 := by
  have he := relIndex_mul_relIndex (⊥ : Subgroup S8) treeGroup pairStabilizer bot_le
    (treeGroup_le_flagStabilizer.trans inf_le_left)
  simp only [relIndex_bot_left,card_treeGroup,pair_card] at he
  omega

/-- The four-pair parabolic moves the unique nonzero vector fixed by the tree Sylow. -/
theorem tree_exists (v : natural (Fin 8)) (hv : v ≠ 0)
    (hfix : ∀ g ∈ treeGroup, naturalRepresentation (Fin 8) g v = v) :
    Nonempty (MovingParabolic (naturalRepresentation (Fin 8)) treeSylow v) := by
  have hSP : (treeSylow : Subgroup S8) ≤ pairStabilizer :=
    treeGroup_le_flagStabilizer.trans inf_le_left
  refine ⟨⟨pairStabilizer, hSP,
    proper_normalizes_of_prime_index treeSylow pairStabilizer hSP ?_, ?_⟩⟩
  · change (treeGroup.relIndex pairStabilizer).Prime
    rw [tree_pair_index]
    decide
  · apply residual_moves_of_moves _ treeSylow v pairStabilizer hSP hfix
    let g : S8 := Equiv.swap 2 4 * Equiv.swap 3 5
    refine ⟨g, by decide +kernel, ?_⟩
    intro he
    exact (by decide +kernel : g ∉ fourStabilizer)
      ((EightSylowFixed.tree_fixed_stabilizer v hv hfix g).mp he)

/-- An arbitrary Sylow marking is transported to the literal tree calculation. -/
theorem exists_moving (S : Sylow 2 S8) (v : natural (Fin 8)) (hv : v ≠ 0)
    (hfix : ∀ g ∈ (S : Subgroup S8), naturalRepresentation (Fin 8) g v = v) :
    Nonempty (MovingParabolic (naturalRepresentation (Fin 8)) S v) := by
  let ρ := naturalRepresentation (Fin 8)
  obtain ⟨r,hr⟩ := MulAction.exists_smul_eq S8 S treeSylow
  let e := MulAut.conj r
  have hS : S.mapSurjective (f := e.toMonoidHom) e.surjective = treeSylow := by
    apply Sylow.ext
    change ((r • S : Sylow 2 S8) : Subgroup S8) = (treeSylow : Subgroup S8)
    rw [hr]
  let f : natural (Fin 8) ≃ₗ[ZMod 2] natural (Fin 8) :=
    LinearEquiv.ofLinearMap (ρ r) (ρ r⁻¹)
      (by change ρ r * ρ r⁻¹ = 1; rw [← map_mul,mul_inv_cancel,map_one])
      (by change ρ r⁻¹ * ρ r = 1; rw [← map_mul,inv_mul_cancel,map_one])
  have hf (g : S8) (w : natural (Fin 8)) : f (ρ g w) = ρ (e g) (f w) := by
    change ρ r (ρ g w) = ρ (r * g * r⁻¹) (ρ r w)
    simp only [← Module.End.mul_apply,← map_mul]
    congr 2
    group
  have hv' : f v ≠ 0 := fun he => hv (f.injective (he.trans (map_zero f).symm))
  have hfix' : ∀ g ∈ treeGroup, ρ g (f v) = f v := by
    intro g hg
    have hm : g ∈ (S : Subgroup S8).map e.toMonoidHom := by
      change g ∈ ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 S8) : Subgroup S8)
      rw [hS]
      exact hg
    obtain ⟨a,ha,rfl⟩ := hm
    exact (hf a v).symm.trans (congrArg f (hfix a ha))
  obtain ⟨d⟩ := tree_exists (f v) hv' hfix'
  have d' : MovingParabolic ρ (S.mapSurjective (f := e.toMonoidHom) e.surjective) (f v) := hS.symm ▸ d
  exact ⟨MovingParabolic.comap ρ ρ e f hf S v d'⟩

/-- Actual intertwining maps transfer the eight-point calculation to its source carrier. -/
theorem exists_of_equiv {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (e : D ≃* S8) (f : ρ.Equiv ((naturalRepresentation (Fin 8)).comp e.toMonoidHom))
    (S : Sylow 2 D) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g ∈ (S : Subgroup D), ρ g w = w) :
    Nonempty (MovingParabolic ρ S w) := by
  have hf (g : D) (v : W) : f (ρ g v) = naturalRepresentation (Fin 8) (e g) (f v) :=
    Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g v
  have hw' : f w ≠ 0 := fun he => hw (f.injective (he.trans (map_zero f).symm))
  have hfix' : ∀ g ∈ ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 S8) : Subgroup S8),
      naturalRepresentation (Fin 8) g (f w) = f w := by
    rintro g ⟨a,ha,rfl⟩
    exact (hf a w).symm.trans (congrArg f (hfix a ha))
  obtain ⟨d⟩ := exists_moving _ (f w) hw' hfix'
  exact ⟨MovingParabolic.comap ρ _ e f.toLinearEquiv hf S w d⟩

end Representation.SmallDisplacementParabolics.OrthogonalEight
