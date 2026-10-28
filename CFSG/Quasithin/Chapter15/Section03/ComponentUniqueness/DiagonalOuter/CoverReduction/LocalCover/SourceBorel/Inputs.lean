module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Contracts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Definitions

/-!
# Inputs and intermediate outputs for the source Borel construction

The fixed local data, ordinary component, and earlier conclusions retain the
source's outside family and relative subgroup conventions. The Borel is
N_L(S ∩ L). `BorelStep` and `CyclicPlaneChoice` are intermediate outputs whose
constructors remain proof obligations, not additional standing hypotheses.
The former is independent of the orientation of the natural binary planes;
the latter is an action problem for an arbitrary two-perfect subgroup with
an order-three two-core quotient.

`MatrixTests` states the two intrinsic projective calculations used by the
transport argument: rigidity of the theta subgroup of a Sylow normalizer,
and root containment for its invariant nontrivial unipotent subgroups.
The root is allowed an inner conjugate. These explicit model inputs do not
identify either original plane with a center or an ambient centralizer.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.2--12, 15.3.25, 15.3.33--37, and the proof of 15.3.38,
printed pp.1121--1125 and 1134--1136.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

/-- The Borel is the actual Sylow normalizer inside the component. -/
def borel (S L : Subgroup G) : Subgroup G :=
  L ⊓ normalizer (S ⊓ L : Subgroup G)

/-- Earlier local conclusions, uniform over the actual outside family.
The module-normalizer equality is the standing choice of M; the remaining
fields are the indicated inputs from 15.3.11, 15.3.25, and 15.3.36.
No Borel, plane orientation, or conclusion of 15.3.38 is included. -/
structure Earlier (d : CharacteristicTwo.LocalData G) : Prop where
  sylow : OutsideSylowControl d.Yplus d.S d.M
  odd : ∀ J ∈ d.Hplus, pPrimeCore 2 J = ⊥
  rank : ∀ J ∈ d.Hplus, primeRank 3 J ≤ 2
  theta_eq : ∀ J ∈ d.Hplus, theta (d.M ⊓ J) = d.Yplus
  normalizer_eq : ∀ J ∈ d.Hplus,
    J ⊓ normalizer (d.Yplus : Set G) = d.M ⊓ J
  intersection_characteristic_two : ∀ J ∈ d.Hplus,
    generalizedFitting (d.M.subgroupOf J) = pCore 2 (d.M.subgroupOf J)
  exclusion : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J
  solvable : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G)
  quotient_exponent : Monoid.exponent (d.Yplus ⧸ pCore 2 d.Yplus) ∣ 3
  shadow : RankTwo.RankTwoShadow d.Yplus d.S
  local_core : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)
  module_normalizer : normalizer (d.V : Set G) = d.M

/-- The selected ordinary component in the contrary rank-two branch. -/
structure Setup (d : CharacteristicTwo.LocalData G) (I L : Subgroup G) : Prop where
  outside : I ∈ d.Hplus
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  component_rank : primeRank 3 L = 2
  residual_rank : primeRank 3 d.Yplus = 2
  not_le : ¬ d.Yplus ≤ L

/-- The two intrinsic projective calculations used after Borel placement.
They concern actual Sylow subgroups and automorphisms of the marked matrix
group. They make no choice of an ambient plane or a coordinate conjugator. -/
structure MatrixTests {L : Subgroup G} {q : ℕ} (c : ProjectiveMarking L q) : Prop where
  rigid : ∀ P : Sylow 2 PSL(3,c.F), ∀ α : MulAut PSL(3,c.F),
    (∀ x ∈ theta (normalizer (P : Set PSL(3,c.F))), α x = x) → α = 1
  root : ∀ P : Sylow 2 PSL(3,c.F), ∀ W : Subgroup PSL(3,c.F),
    W ≤ (P : Subgroup PSL(3,c.F)) →
    normalizer (P : Set PSL(3,c.F)) ≤ normalizer (W : Set PSL(3,c.F)) →
    W ≠ ⊥ → ∃ g : PSL(3,c.F),
      (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter c.F).map
        (MulAut.conj g).toMonoidHom ≤ W

/-- Intermediate OUTPUT of the Borel argument. Its constructor must establish
these facts from the earlier local hypotheses and explicit intrinsic model
calculations. In particular, this record is not an earlier source theorem. -/
structure BorelStep (d : CharacteristicTwo.LocalData G) (I L : Subgroup G)
    {q : ℕ} (c : ProjectiveMarking L q) where
  invariant : d.Yplus ⊔ d.S ≤ normalizer (borel d.S L : Set G)
  characteristic_two : generalizedFitting (borel d.S L) = pCore 2 (borel d.S L)
  residual_le : componentPart d.Yplus L ≤ borel d.S L
  residual_generated : theta (componentPart d.Yplus L) = componentPart d.Yplus L
  theta_core : (theta (borel d.S L)).pCoreIn 2 = d.S ⊓ L
  theta_quotient : Nat.card
    (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) = 3
  normalizer_eq : I ⊓ normalizer (borel d.S L : Set G) = d.M ⊓ I
  P : Sylow 2 PSL(3,c.F)
  sylow_image : (d.S.subgroupOf L).map (projectiveMap c) = P
  borel_image : ((borel d.S L).subgroupOf L).map (projectiveMap c) =
    normalizer (P : Set PSL(3,c.F))
  theta_image : ((theta (borel d.S L)).subgroupOf L).map (projectiveMap c) =
    theta (normalizer (P : Set PSL(3,c.F)))

/-- Intermediate OUTPUT of the cyclic actor calculation in the natural
orthogonal module. No component or projective marking occurs in this problem. -/
structure CyclicPlaneChoice (d : CharacteristicTwo.LocalData G) (A : Subgroup G) where
  W₁ : Subgroup G
  W₂ : Subgroup G
  planes : PlaneOrder d.V₁ d.V₂ W₁ W₂
  centralizes : A ≤ centralizer (W₁ : Set G)
  commutator : ⁅d.V, A⁆ = W₂
  moves : ⁅W₂, A⁆ = W₂
  t : G
  t_mem : t ∈ (d.T : Subgroup G)
  sylow_invariant : d.S.map (MulAut.conj t).toMonoidHom = d.S
  first_interchange : W₁.map (MulAut.conj t).toMonoidHom = W₂
  second_interchange : W₂.map (MulAut.conj t).toMonoidHom = W₁

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
