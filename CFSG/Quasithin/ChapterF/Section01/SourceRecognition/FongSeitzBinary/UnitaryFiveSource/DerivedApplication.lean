module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.DerivedHermitian
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.ActorCartanApplication

/-!
# Original-source Hermitian coordinates on the U₅ derived subgroup

The genuine original SL₂ epimorphism, with its intrinsic-core kernel,
constructs the full linear actor. DerivedHermitian then constructs the
Hermitian realization of its actual radical-derived subgroup. Every actor
has its original endpoint representative, and the action is exactly the
one determined by that epimorphism and the constructed field equivalence.
The aligned version uses the specified source reflection and the actual
simple root, via the existing complete rank-one pinning.

The original specialization expands this into the literal Q.q(a*v*a⁻¹)
formula. It uses only a subset of the authorized earlier U₅ profile inputs,
with both orientations and all positive binary degrees retained. The full
nonabelian-root lift, synchronization with the SU₃ natural coordinates,
and the remaining presentation equations are still required for FiveData.
Source: DGS (11.8)(b); Fong--Seitz I (6A)(c), II (8.21)--(8.23), p.206.
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open Representation.OrthogonalFourMinus.FiniteModel
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)

include h hK hE hfixed hJ hm hij hVi hVj s hf hk ν

/-- Construct the Hermitian coordinates from the original linear quotient and unitary panel marking. -/
theorem marked_derived_realization :
    ∃ (μ : rankOne Q split i ≃* SL(2,K)) (ξ : K ≃+* Field n)
      (c : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q mark i a.val = r ∧ μ r = f a) ∧
      ∀ (r : rankOne Q split i) (p : Space n),
        (r : X ⧸ Q.D) * (c (.ofAdd p) : X ⧸ Q.D) * (r : X ⧸ Q.D)⁻¹ =
          c (.ofAdd (action n (Matrix.SpecialLinearGroup.map ξ.toRingHom (μ r)) p)) := by
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal :=
    QuadrangleStructure.marked_sylow_factor_normal Q mark h split i
  obtain ⟨μ,_,_,hμ⟩ := QuadrangleStructure.marked_linear_localGroup Q mark h split i s hVi _
    (subgroupOf_mono _ le_sup_left) f hf hk
  obtain ⟨ξ,c,hc⟩ := linear_derived_realization Q split J n hK hE hfixed hJ hm i j hij hVi hVj s μ ν
  exact ⟨μ,ξ,c,hμ,hc⟩

/-- Construct the realization with the complete actor pinned to the specified reflection. -/
theorem marked_aligned_derived_realization :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q mark h split i hVi f hf hk
    ∃ (ξ : K ≃+* Field n)
      (c : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))),
      ∀ (g : SL(2,Field n)) (p : Space n),
        Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.fieldRelabelledActor
            Q split i hVi μ₀ s n ξ g * (c (.ofAdd p) : X ⧸ Q.D) *
            (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.fieldRelabelledActor
              Q split i hVi μ₀ s n ξ g)⁻¹ =
          c (.ofAdd (action n g p)) := by
  exact aligned_derived_realization Q split J n hK hE hfixed hJ hm i j hij hVi hVj s ν _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
variable {G K E : Type*} [Group G]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)

include h hK hE hfixed hJ hm hij hVi hVj s hf hk ν

/-- The same construction retains the original Q.q lift of every linear actor. -/
theorem original_derived_realization :
    ∃ (μ : rankOne Q split i ≃* SL(2,K)) (ξ : K ≃+* Field n)
      (c : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup ((generated L S) ⧸ Q.D))),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      ∀ (r : rankOne Q split i) (p : Space n),
        (r : (generated L S) ⧸ Q.D) * (c (.ofAdd p) : (generated L S) ⧸ Q.D) *
            (r : (generated L S) ⧸ Q.D)⁻¹ =
          c (.ofAdd (action n (Matrix.SpecialLinearGroup.map ξ.toRingHom (μ r)) p)) := by
  obtain ⟨μ,ξ,c,hμ,hc⟩ := marked_derived_realization Q split (originalMarkedIso Q) h J n
    hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν
  refine ⟨μ,ξ,c,?_,hc⟩
  intro r
  obtain ⟨a,ha,he⟩ := hμ r
  exact ⟨a,(original_endpointMap_apply Q i a.val).symm.trans ha,he⟩

/-- Evaluate conjugation on literal original actor and derived-subgroup representatives. -/
theorem original_derived_representatives :
    ∃ (μ : rankOne Q split i ≃* SL(2,K)) (ξ : K ≃+* Field n)
      (c : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup ((generated L S) ⧸ Q.D))),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      ∀ (a v : generated L S) (ha : Q.q a ∈ rankOne Q split i)
        (hv : Q.q v ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆),
        ∃ w : (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup ((generated L S) ⧸ Q.D)),
          (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
          (c.symm w).toAdd = action n
            (Matrix.SpecialLinearGroup.map ξ.toRingHom (μ ⟨Q.q a,ha⟩))
              (c.symm ⟨Q.q v,hv⟩).toAdd := by
  obtain ⟨μ,ξ,c,hμ,hc⟩ := original_derived_realization Q split h J n
    hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν
  refine ⟨μ,ξ,c,hμ,?_⟩
  intro a v ha hv
  let w := remainderDerivedAction Q split i hVi ⟨Q.q a,ha⟩ ⟨Q.q v,hv⟩
  refine ⟨w,?_,?_⟩
  · rw [remainderDerivedAction_apply,map_mul,map_mul,map_inv]
  · have he := hc ⟨Q.q a,ha⟩ (c.symm ⟨Q.q v,hv⟩).toAdd
    have hw : w = c (.ofAdd (action n
        (Matrix.SpecialLinearGroup.map ξ.toRingHom (μ ⟨Q.q a,ha⟩))
          (c.symm ⟨Q.q v,hv⟩).toAdd)) := by
      apply Subtype.ext
      dsimp only [w]
      rw [remainderDerivedAction_apply]
      simpa only [ofAdd_toAdd,MulEquiv.apply_symm_apply] using he
    rw [hw,MulEquiv.symm_apply_apply]
    rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
