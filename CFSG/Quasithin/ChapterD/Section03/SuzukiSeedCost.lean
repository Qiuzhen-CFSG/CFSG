module
public import Theory.Representation.Suzuki.SupportMultiplicity
public import CFSG.Quasithin.ChapterD.Section02.Inheritance

/-!
# Strong seed costs under a commuting Suzuki action

The pointwise kernel of an actor is unchanged on a seed's commuting orbit.
The inherited starred-actor bound therefore gives the orbit at most twice
the rank visible on the seed. If the seed costs at least that rank, the
homogeneous orbit contains at most two copies. A fixed-free Suzuki actor
forces at least three, so every such seed has a strong offender instead.

SuzukiNormalizedSupport uses this strict inequality to exclude the natural
binary SL2 seed, without assuming faithfulness of the actor on its support.
Source: Aschbacher--Smith A.1.41--42, D.2.7 and D.3.9,
printed pp.31--32,180,200--201; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every invariant simple seed moved by a starred actor commuting with a
fixed-free Suzuki group has a strong offender on its actual action image. -/
theorem suzuki_commuting_seed_strong
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (X A : Subgroup G) (hA : A ∈ QhatStar ρ)
    (hc : K ≤ centralizer (X : Set G)) (hAX : A ≤ X)
    (R : Submodule (ZMod 2) V) (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation)
    (hmove : ¬ R ≤ fixedSpace ρ A) :
    fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) <
      rank (restrictedSubgroup ρ R A) := by
  let O := orbitSpan ρ K R
  have hRO : R ≤ O := le_orbitSpan ρ K R
  have hAO : A ≤ subspaceStabilizer ρ O := hAX.trans
    (CommutingMultiplicity.orbit_invariant_of_commuting ρ X K hc R hR)
  have hAR : A ≤ subspaceStabilizer ρ R := hAX.trans hR
  have hmoveO : ¬ O ≤ fixedSpace ρ A := fun hh => hmove (hRO.trans hh)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hp := IsElementaryAbelian.isPGroup 2 A
  have hk := CommutingMultiplicity.kernel_commuting_orbit ρ A K
    (hc.trans (centralizer_le hAX)) R
  have h₁ := rank_subspaceKernel_add_image ρ O A hAO hp
  have h₂ := rank_subspaceKernel_add_image ρ R A hAR hp
  have hr : rank (restrictedSubgroup ρ O A) = rank (restrictedSubgroup ρ R A) := by
    change subspaceKernel ρ O A = _ at hk
    rw [hk] at h₁
    omega
  have hb := RPlusBound.restricted ρ
    (show A ∈ RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,QhatStar.mem_RPlus ρ hA⟩)
    O hAO hmoveO
  have hu := (actionRatio_le_nat_iff _ hb.1 2).mp hb.2
  rw [hr] at hu
  by_contra! hcost
  have hd := CommutingMultiplicity.commuting_orbit_degree_le_two ρ X K A hc hAX R hR hi
    hmove (hu.trans (Nat.mul_le_mul_left 2 hcost))
  have hl := Suzuki.commuting_support_triple_degree ρ K hfix m hm e X hc R hR hi
  let : Nontrivial R := Subrepresentation.irreducible_module_nontrivial
    (invariantSubspace ρ X R hR).toRepresentation (inst := hi)
  have hpos := Module.finrank_pos (R := ZMod 2) (M := R)
  omega

end CFSG.Quasithin.ChapterD
