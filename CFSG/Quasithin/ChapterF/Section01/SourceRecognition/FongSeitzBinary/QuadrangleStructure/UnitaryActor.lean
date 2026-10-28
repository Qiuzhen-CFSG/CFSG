module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryLinearActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryCommutators
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorKernel

/-!
# The full U₅ actor and its covering centre

The DGS (11.8)(c) actor is a covering actor.  The faithful panel image is
`localGroup`, hence is projective unitary; the actor itself is the full
`rankOne` subgroup and retains the scalar kernel.  This file gives the
literal interface for the actor part of that source profile.  It deliberately
keeps the actor homomorphism, its bijectivity and its projective marking as
separate fields: a numerical PSU₃ label is not a cover identification.

Once the actual source homomorphism is supplied, the adapter constructs the
SU₃ equivalence and exposes the intrinsic scalar kernel.  The completed
commutator and linear-section adapters remain available next to this actor
interface, with all earlier DGS hypotheses still visible.

Source: DGS (11.8)(b,c,f), pp.175--176; Fong--Seitz I (5C), (6A)(c),
pp.26,37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The actual DGS full-actor data on a marked quotient.  The homomorphism is
the source actor map, not a map reconstructed from the projective label. -/
structure UnitaryActorProfile
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hV : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : localGroup Q split j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) where
  hom : rankOne Q split j →* J.specialSubgroup
  surjective : Function.Surjective hom
  injective : Function.Injective hom
  projective : ∀ r : rankOne Q split j,
    ν (rankOneLocalEquiv Q split j hV (QuotientGroup.mk r)) =
      J.specialToProjective (hom r)

/-- The covering actor equivalence and the scalar kernel supplied by the
literal full-actor profile. -/
theorem marked_unitary_full_actor
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (_hn : 0 < n)
    (_hE : Nat.card E = (2^n)^2)
    (_hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (_hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {hV : simpleRemainder Q split j ≤ localKernel Q j}
    (ν : localGroup Q split j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (d : UnitaryActorProfile Q split j J hV ν)
    (hZ : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥) :
    ∃ κ : rankOne Q split j ≃* J.specialSubgroup,
      (∀ r : rankOne Q split j,
        ν (rankOneLocalEquiv Q split j hV (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup := by
  let κ : rankOne Q split j ≃* J.specialSubgroup :=
    MulEquiv.ofBijective d.hom ⟨d.injective, d.surjective⟩
  refine ⟨κ, ?_, J.specialToProjective_ker_eq_center hZ⟩
  intro r
  exact d.projective r

/- The projective marking also transports the covering centre.  This is the
   point at which the faithful PSU₃ image is converted back to the literal
   SU₃ actor; no scalar kernel is quotiented away. -/
theorem marked_unitary_full_actor_center
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {hV : simpleRemainder Q split j ≤ localKernel Q j}
    (ν : localGroup Q split j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (_d : UnitaryActorProfile Q split j J hV ν)
    (κ : rankOne Q split j ≃* J.specialSubgroup)
    (hκ : ∀ r : rankOne Q split j,
      ν (rankOneLocalEquiv Q split j hV (QuotientGroup.mk r)) =
        J.specialToProjective (κ r))
    (hZ : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥) :
    center (rankOne Q split j) =
      (center J.specialSubgroup).comap κ.toMonoidHom := by
  apply le_antisymm
  · intro r hr
    rw [Subgroup.mem_comap]
    change κ r ∈ center J.specialSubgroup
    apply mem_center_iff.mpr
    intro z
    obtain ⟨s, rfl⟩ := κ.surjective z
    simpa only [map_mul] using congrArg κ (mem_center_iff.mp hr s)
  · intro r hr
    change κ r ∈ center J.specialSubgroup at hr
    have hz : κ r ∈ center J.specialSubgroup := hr
    have hpc : J.specialToProjective (κ r) ∈
        center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := J.specialToProjective_surjective y
      simpa only [map_mul] using
        congrArg J.specialToProjective (mem_center_iff.mp hz z)
    have hpc' : J.specialToProjective (κ r) = 1 := by
      simpa only [hZ, mem_bot] using hpc
    have hq : rankOneLocalEquiv Q split j hV (QuotientGroup.mk r) = 1 := by
      apply ν.injective
      rw [hκ, hpc']
      exact (map_one ν).symm
    have ha : rankOneAction Q split j r = 1 := by
      rw [← rankOneLocalEquiv_apply Q split j hV r]
      exact congrArg Subtype.val hq
    exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.rankOneAction_ker_le_center
      Q split j (MonoidHom.mem_ker.mpr ha)

include L S
/-- The literal source profile is retained on the original quotient. -/
theorem original_unitary_full_actor
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits) (j : Fin 2)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {hV : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j}
    (ν : localGroup Q₀ split₀ j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (d : UnitaryActorProfile Q₀ split₀ j J hV ν)
    (hZ : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥) :
    ∃ κ : rankOne Q₀ split₀ j ≃* J.specialSubgroup,
      (∀ r : rankOne Q₀ split₀ j,
        ν (rankOneLocalEquiv Q₀ split₀ j hV (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup := by
  exact marked_unitary_full_actor Q₀ split₀ j J hn hE hfixed hJ ν d hZ

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
