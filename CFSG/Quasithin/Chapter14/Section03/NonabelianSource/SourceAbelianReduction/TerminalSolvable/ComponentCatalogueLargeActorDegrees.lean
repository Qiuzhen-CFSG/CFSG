module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActor
public import CFSG.Quasithin.ChapterG.Section10.NumericalGeometry
public import Theory.Representation.BinaryPlaneSolvable
public import Theory.SpecificGroups.G2.BinaryElementaryRank

/-!
# Numerical assembly for the original larger-actor branch

The source context below contains only the original hypotheses. Nonsolvability
and the faithful alternating action give degree at least four. Failure of the
small-actor bound gives actor dimension at least half the even degree. In degree
six an actual full G₂(2) equivalence supplies the opposite actor bound, using
the concrete Sylow calculation, so the actor has dimension exactly three.

Two independent source steps remain: bounding the degree above by six, and
recognizing the full dotted group when the degree is six. The conditional
assembly here combines these with the proved numerical facts and applies the
existing component consumer. Neither missing source step is asserted here.

Source: Aschbacher--Smith 14.3.13--14, printed pp.993--994; G.11.2,
printed pp.364--367. The exclusions from 12.8.13 are needed by the remaining
recognition proofs, rather than assumed as a classification certificate.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The literal original source prefix for the larger-actor degree problem.
No degree upper bound, model recognition, or classification conclusion is a field. -/
structure LargeActorSource {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M Mc : Subgroup G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat) : Prop where
  simple : IsSimpleQTKE KnownSimple.IsKnownSimple G
  empty : MainForward.faithfulLocalComponents T = ∅
  maximal : IsOrderingMaximal T M
  unique_overgroup : maximalTwoLocalOvergroups
    (centralizer (centralInvolutions T : Set G)) = {Mc}
  many_overgroups : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  seed_card : Nat.card (localModule T M) = 4
  centralizer_quotient : Nonempty
    ((M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
  not_model : ¬ ClassificationModels.IsTheoremEModel G
  nonabelian : ¬ IsMulCommutative F.U
  parabolic_mem : g ∈ F.P (sourceResidual M Mc)
  normalizer_not_mem : g ∉ F.H
  nonsolvable : ¬ Group.IsSolvable F.TerminalHdot
  hypothesis : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))
  large_actor : ¬ (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
    finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- Alternating parity is on the actual central quotient U/Z(U). -/
theorem even_degree : Even (finrank (ZMod 2) (Additive F.Uhat)) :=
  AlternatingForm.even_finrank B s.hypothesis.alternating s.hypothesis.nondegenerate

/-- The nonsolvable source group cannot act faithfully on a binary plane.
Together with alternating parity this excludes every degree below four. -/
theorem four_le_degree : 4 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
  have htwo := s.hypothesis.two_le_dimension
  obtain ⟨n, hn⟩ := s.even_degree
  by_contra hsmall
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 2 := by omega
  let a : F.TerminalHdot →* BinaryLinear.GL (Additive F.Uhat) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive F.Uhat)).toMonoidHom.comp
      F.terminalRepresentation.asGroupHom
  have ha : Function.Injective a := by
    intro x y hxy
    apply s.hypothesis.faithful
    apply LinearMap.ext
    intro w
    exact congrArg (fun e : BinaryLinear.GL (Additive F.Uhat) => e w) hxy
  let : Group.IsSolvable (BinaryLinear.GL (Additive F.Uhat)) :=
    BinaryLinear.SmallParabolicLevi.linearGroup_solvable_of_finrank_two hd
  exact s.nonsolvable (Group.isSolvable_of_isSolvable_injective ha)

/-- Failure of the small-actor inequality gives the literal half-degree bound. -/
theorem half_degree_le_actor :
    finrank (ZMod 2) (Additive F.Uhat) / 2 ≤
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have h := s.large_actor
  omega

/-- The actual larger actor has dimension at least two. -/
theorem two_le_actor : 2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  have hd := s.four_le_degree
  have hm := s.half_degree_le_actor
  omega

/-- Recognition of the full dotted group supplies the upper actor bound;
the original larger-actor hypothesis supplies the lower bound. -/
theorem actor_eq_three_of_six_binaryG2
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (e : F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)) :
    finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 := by
  have hu := Atlas.G2.binary_actor_finrank_le_three e (F.terminalDot (F.X g))
  have hl := s.half_degree_le_actor
  omega

/-- Conditional numerical assembly. The upper degree bound and degree-six
full-group recognition are independent source obligations, still to be proved. -/
theorem degree_cases_of_bound_and_six_recognition
    (hbound : finrank (ZMod 2) (Additive F.Uhat) ≤ 6)
    (hsix : finrank (ZMod 2) (Additive F.Uhat) = 6 →
      Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))) :
    (finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
      2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
    (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
      Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))) := by
  have hl := s.four_le_degree
  obtain ⟨n, hn⟩ := s.even_degree
  by_cases hd : finrank (ZMod 2) (Additive F.Uhat) = 4
  · exact Or.inl ⟨hd, s.two_le_actor⟩
  have hd6 : finrank (ZMod 2) (Additive F.Uhat) = 6 := by omega
  obtain ⟨e⟩ := hsix hd6
  exact Or.inr ⟨hd6, s.actor_eq_three_of_six_binaryG2 hd6 e, ⟨e⟩⟩

/-- The actual larger-actor component consumer with the numerical assembly
supplied above. Degree-four recognition and A₆ exclusion remain with their
existing independent owners. -/
theorem component_of_bound_and_six_recognition
    (hbound : finrank (ZMod 2) (Additive F.Uhat) ≤ 6)
    (hrecognize : finrank (ZMod 2) (Additive F.Uhat) = 6 →
      Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    (∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
      ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
    (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
      Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
      F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
        pCore 2 (K.subgroupOf F.H)) :=
  source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis
    (s.degree_cases_of_bound_and_six_recognition hbound hrecognize) hfour hsix

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
