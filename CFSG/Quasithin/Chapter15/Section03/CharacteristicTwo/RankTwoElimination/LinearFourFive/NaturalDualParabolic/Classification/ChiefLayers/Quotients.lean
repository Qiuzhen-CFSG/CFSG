module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.ChiefLayers.Flag

/-!
# The two marked module quotients of the point parabolic

Projection in the original natural-plus-dual coordinates gives surjections
B → V/⟨x⟩ and C → ann(x), with kernels A and B respectively. The first
isomorphism theorem gives the actual section isomorphisms. Their formulas
on representatives intertwine conjugation by the original P with quotientActor
and annihilatorActor. Evaluation makes the latter the contragredient of the
former, under the same marking of P/O₂(P).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- Coordinates of B in the original natural summand. -/
noncomputable def naturalCoordinates (h : NaturalDual d L) :
    naturalSubgroup h ≃* Multiplicative (Space 4) :=
  (coordinateEquiv h naturalSpace).symm.trans naturalSpaceEquiv.toAddEquiv.toMultiplicative

/-- Coordinates of C retaining its natural and annihilator components. -/
noncomputable def mixedCoordinates (h : NaturalDual d L) (x : Space 4) :
    mixedSubgroup h x ≃* Multiplicative (Space 4 × annihilator x) :=
  (coordinateEquiv h (mixedSpace x)).symm.trans (mixedSpaceEquiv x).toAddEquiv.toMultiplicative

@[simp] theorem naturalCoordinates_symm_apply (h : NaturalDual d L)
    (v : Multiplicative (Space 4)) :
    ((naturalCoordinates h).symm v : G) = embed h (Multiplicative.ofAdd (v.toAdd, 0)) := rfl

@[simp] theorem mixedCoordinates_symm_apply (h : NaturalDual d L) (x : Space 4)
    (v : Multiplicative (Space 4 × annihilator x)) :
    ((mixedCoordinates h x).symm v : G) =
      embed h (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.val)) := rfl

/-- The quotient map from B, expressed through its original embedding. -/
noncomputable def naturalProjection (h : NaturalDual d L) (x : Space 4) :
    naturalSubgroup h →* Multiplicative (pointQuotient x) :=
  (line x).mkQ.toAddMonoidHom.toMultiplicative.comp (naturalCoordinates h).toMonoidHom

/-- Projection from C onto its annihilator component. -/
noncomputable def mixedProjection (h : NaturalDual d L) (x : Space 4) :
    mixedSubgroup h x →* Multiplicative (annihilator x) :=
  (LinearMap.snd (ZMod 2) (Space 4) (annihilator x)).toAddMonoidHom.toMultiplicative.comp
    (mixedCoordinates h x).toMonoidHom

@[simp] theorem naturalProjection_coordinates (h : NaturalDual d L) (x : Space 4)
    (v : Multiplicative (Space 4)) :
    naturalProjection h x ((naturalCoordinates h).symm v) =
      Multiplicative.ofAdd ((line x).mkQ v.toAdd) := by
  simp [naturalProjection]

@[simp] theorem mixedProjection_coordinates (h : NaturalDual d L) (x : Space 4)
    (v : Multiplicative (Space 4 × annihilator x)) :
    mixedProjection h x ((mixedCoordinates h x).symm v) = Multiplicative.ofAdd v.toAdd.2 := by
  simp [mixedProjection]

theorem naturalProjection_surjective (h : NaturalDual d L) (x : Space 4) :
    Function.Surjective (naturalProjection h x) := by
  intro q
  obtain ⟨v, hv⟩ := (line x).mkQ_surjective q.toAdd
  exact ⟨(naturalCoordinates h).symm (Multiplicative.ofAdd v), by
    simpa only [naturalProjection_coordinates, toAdd_ofAdd, ofAdd_toAdd] using congrArg Multiplicative.ofAdd hv⟩

theorem mixedProjection_surjective (h : NaturalDual d L) (x : Space 4) :
    Function.Surjective (mixedProjection h x) := by
  intro q
  exact ⟨(mixedCoordinates h x).symm (Multiplicative.ofAdd (0, q.toAdd)),
    mixedProjection_coordinates h x _⟩

/-- The kernel is A, as a subgroup of the actual B. -/
theorem naturalProjection_ker (h : NaturalDual d L) (x : Space 4) :
    (naturalProjection h x).ker = (lineSubgroup h x).subgroupOf (naturalSubgroup h) := by
  ext b
  obtain ⟨v, rfl⟩ := (naturalCoordinates h).symm.surjective b
  change naturalProjection h x ((naturalCoordinates h).symm v) = 1 ↔
    ((naturalCoordinates h).symm v : G) ∈ lineSubgroup h x
  rw [naturalProjection_coordinates, naturalCoordinates_symm_apply, ofAdd_eq_one]
  change (Submodule.Quotient.mk v.toAdd = (0 : pointQuotient x)) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change v.toAdd ∈ line x ↔ embed h (Multiplicative.ofAdd (v.toAdd, 0)) ∈
    coordinateSubgroup h (lineSpace x)
  rw [embed_mem_coordinateSubgroup]
  exact ⟨fun hv => ⟨hv, Submodule.zero_mem _⟩, fun hv => hv.1⟩

/-- The kernel is B, as a subgroup of the actual C. -/
theorem mixedProjection_ker (h : NaturalDual d L) (x : Space 4) :
    (mixedProjection h x).ker = (naturalSubgroup h).subgroupOf (mixedSubgroup h x) := by
  ext c
  obtain ⟨v, rfl⟩ := (mixedCoordinates h x).symm.surjective c
  change mixedProjection h x ((mixedCoordinates h x).symm v) = 1 ↔
    ((mixedCoordinates h x).symm v : G) ∈ naturalSubgroup h
  rw [mixedProjection_coordinates, mixedCoordinates_symm_apply, ofAdd_eq_one]
  change v.toAdd.2 = 0 ↔ embed h (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.val)) ∈
    coordinateSubgroup h naturalSpace
  rw [embed_mem_coordinateSubgroup]
  exact ⟨fun hv => ⟨Submodule.mem_top, congrArg Subtype.val hv⟩,
    fun hv => Subtype.ext hv.2⟩

instance lineInNatural_normal (h : NaturalDual d L) (x : Space 4) :
    ((lineSubgroup h x).subgroupOf (naturalSubgroup h)).Normal := by
  rw [← naturalProjection_ker]
  infer_instance

instance naturalInMixed_normal (h : NaturalDual d L) (x : Space 4) :
    ((naturalSubgroup h).subgroupOf (mixedSubgroup h x)).Normal := by
  rw [← mixedProjection_ker]
  infer_instance

/-- The actual quotient B/A is the natural three-space V/⟨x⟩. -/
noncomputable def naturalQuotientEquiv (h : NaturalDual d L) (x : Space 4) :
    (naturalSubgroup h ⧸ (lineSubgroup h x).subgroupOf (naturalSubgroup h)) ≃*
      Multiplicative (pointQuotient x) :=
  (QuotientGroup.quotientMulEquivOfEq (naturalProjection_ker h x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (naturalProjection h x)
      (naturalProjection_surjective h x))

/-- The actual quotient C/B is the three-dimensional annihilator. -/
noncomputable def mixedQuotientEquiv (h : NaturalDual d L) (x : Space 4) :
    (mixedSubgroup h x ⧸ (naturalSubgroup h).subgroupOf (mixedSubgroup h x)) ≃*
      Multiplicative (annihilator x) := by
  let e : (mixedSubgroup h x ⧸ (naturalSubgroup h).subgroupOf (mixedSubgroup h x)) ≃*
      (mixedSubgroup h x ⧸ (mixedProjection h x).ker) :=
    QuotientGroup.quotientMulEquivOfEq (mixedProjection_ker h x).symm
  let k : (mixedSubgroup h x ⧸ (mixedProjection h x).ker) ≃*
      Multiplicative (annihilator x) :=
    @QuotientGroup.quotientKerEquivOfSurjective (mixedSubgroup h x) inferInstance
      (Multiplicative (annihilator x)) inferInstance (mixedProjection h x)
      (mixedProjection_surjective h x)
  exact e.trans k

@[simp] theorem naturalQuotientEquiv_mk (h : NaturalDual d L) (x : Space 4)
    (b : naturalSubgroup h) :
    naturalQuotientEquiv h x (QuotientGroup.mk' _ b) = naturalProjection h x b := rfl

@[simp] theorem mixedQuotientEquiv_mk (h : NaturalDual d L) (x : Space 4)
    (c : mixedSubgroup h x) :
    mixedQuotientEquiv h x (QuotientGroup.mk' _ c) = mixedProjection h x c := rfl

/-- Literal conjugation in an invariant subgroup, with its original carrier. -/
def conjugate (P H : Subgroup G) (hH : P ≤ normalizer (H : Set G)) (p : P) (a : H) : H :=
  ⟨(p : G) * (a : G) * (p : G)⁻¹,
    (le_normalizer_iff.mp hH) p p.property a a.property⟩

/-- Natural coordinates intertwine conjugation before taking the quotient. -/
theorem naturalCoordinates_conj (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (v : Multiplicative (Space 4)) :
    conjugate _ _ (naturalSubgroup_normalized h x) p ((naturalCoordinates h).symm v) =
      (naturalCoordinates h).symm (Multiplicative.ofAdd ((pointActor h x p).val v.toAdd)) := by
  apply Subtype.ext
  change (p : G) * ((naturalCoordinates h).symm v : G) * (p : G)⁻¹ = _
  rw [naturalCoordinates_symm_apply, naturalCoordinates_symm_apply]
  have he := embed_conj h (⟨p, point_le h x p.property⟩ : L) (v.toAdd, 0)
  change (p : G) * embed h (Multiplicative.ofAdd (v.toAdd, 0)) * (p : G)⁻¹ = _ at he
  rw [he]
  congr 1
  apply congrArg Multiplicative.ofAdd
  apply Prod.ext
  · exact BinaryLinear.NaturalDualFlag.action_fst _ _
  · apply LinearMap.ext
    intro y
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    rfl

/-- Mixed coordinates intertwine conjugation before taking the quotient. -/
theorem mixedCoordinates_conj (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (v : Multiplicative (Space 4 × annihilator x)) :
    conjugate _ _ (mixedSubgroup_normalized h x) p ((mixedCoordinates h x).symm v) =
      (mixedCoordinates h x).symm (Multiplicative.ofAdd
        ((pointActor h x p).val v.toAdd.1, annihilatorActor h x p v.toAdd.2)) := by
  apply Subtype.ext
  change (p : G) * ((mixedCoordinates h x).symm v : G) * (p : G)⁻¹ = _
  rw [mixedCoordinates_symm_apply, mixedCoordinates_symm_apply]
  have he := embed_conj h (⟨p, point_le h x p.property⟩ : L) (v.toAdd.1, v.toAdd.2.val)
  change (p : G) * embed h (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.val)) * (p : G)⁻¹ = _ at he
  rw [he]
  congr 1
  apply congrArg Multiplicative.ofAdd
  apply Prod.ext
  · exact BinaryLinear.NaturalDualFlag.action_fst _ _
  · apply LinearMap.ext
    intro y
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    rfl

/-- Equivariance of the natural quotient marking, on every original representative. -/
theorem naturalProjection_conj (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (b : naturalSubgroup h) :
    (naturalProjection h x (conjugate _ _ (naturalSubgroup_normalized h x) p b)).toAdd =
      quotientActor h x p (naturalProjection h x b).toAdd := by
  obtain ⟨v, rfl⟩ := (naturalCoordinates h).symm.surjective b
  rw [naturalCoordinates_conj, naturalProjection_coordinates, naturalProjection_coordinates]
  rfl

/-- Equivariance of the annihilator quotient marking, on every original representative. -/
theorem mixedProjection_conj (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (c : mixedSubgroup h x) :
    (mixedProjection h x (conjugate _ _ (mixedSubgroup_normalized h x) p c)).toAdd =
      annihilatorActor h x p (mixedProjection h x c).toAdd := by
  obtain ⟨v, rfl⟩ := (mixedCoordinates h x).symm.surjective c
  rw [mixedCoordinates_conj, mixedProjection_coordinates, mixedProjection_coordinates]
  rfl

/-- Both quotient markings use the same actor: C/B is the contragredient of B/A. -/
theorem mixedProjection_dual_conj (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (c : mixedSubgroup h x) :
    annihilatorQuotientDual x
      (mixedProjection h x (conjugate _ _ (mixedSubgroup_normalized h x) p c)).toAdd =
      (quotientActor h x p).symm.dualMap
        (annihilatorQuotientDual x (mixedProjection h x c).toAdd) := by
  rw [mixedProjection_conj, quotient_dual_compatibility]

/-- The common marking of the acting quotient on V/⟨x⟩. -/
noncomputable def commonActorEquiv [Finite G] (h : NaturalDual d L) (x : Space 4) :
    (point h x ⧸ pCore 2 (point h x)) ≃* BinaryLinear.GL (pointQuotient x) :=
  (QuotientGroup.quotientMulEquivOfEq (quotientActor_ker h x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quotientActor h x)
      (quotientActor_surjective h x))

@[simp] theorem commonActorEquiv_mk [Finite G] (h : NaturalDual d L) (x : Space 4)
    (p : point h x) :
    commonActorEquiv h x (QuotientGroup.mk' _ p) = quotientActor h x p := rfl

/-- This common marking is exactly the one used by the published L₃(2) identification. -/
theorem commonActorEquiv_projective [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    pointQuotientEquiv h hx = (commonActorEquiv h x).trans
      ((quotientGroupCoordinates hx).trans (projectiveEquivLinear (by decide : 0 < 3)).symm) := rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ChiefLayers
end
