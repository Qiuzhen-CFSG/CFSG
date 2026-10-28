module
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryFullLinearRecognition
public import Theory.Representation.BinaryOffender.IrreducibleExistence
/-!
# Binary three-dimensional moved coordinates for the full normalizer

For an actual SL3(2) subgroup, a three-dimensional moved module is faithful:
a trivial action on its own displacements would be central and hence trivial
by perfectness. Simplicity therefore kills the moved-action kernel. Finite
order recognition identifies the action with the full binary linear group.
The coordinates belong to the original moved space, which is invariant under
the whole normalizer; no centralizer-quotient descent is assumed.

Source application: Aschbacher–Smith, B.5.6(3c),(5) and B.6.9, pp.105,116.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.BinaryFullLinearRecognition
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The original moved space carries the whole normalizer action. -/
noncomputable def fullMovedNormalizerSpace
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) :
    Subrepresentation (ρ.comp (normalizer (L : Set G)).subtype) :=
  invariantSubspace ρ (normalizer (L : Set G)) (subspaceCommutator ρ ⊤ L)
    (subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer _ ⊤ (by intros; trivial)) le_rfl)

/-- Faithful binary coordinates retain the literal normalizer and its subgroup. -/
theorem binary_three_moved_normalizer_natural
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ L) = 3) :
    let σ := (fullMovedNormalizerSpace ρ L).toRepresentation.comp
      (L.subgroupOf (normalizer (L : Set G))).subtype
    ∃ (e : L.subgroupOf (normalizer (L : Set G)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (f : subspaceCommutator ρ ⊤ L ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      ∀ g v, f (σ g v) = (e g).val.mulVec (f v) := by
  let N := normalizer (L : Set G)
  let L₀ := L.subgroupOf N
  let W := fullMovedNormalizerSpace ρ L
  let σ : Representation (ZMod 2) L₀ W.toSubmodule := W.toRepresentation.comp L₀.subtype
  let e : L₀ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (subgroupOfEquivOfLe L.le_normalizer).trans eL
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
      (by simp : Nat.card (ZMod 2) = 2^1) (by decide)).isSimpleGroup
  let : IsSimpleGroup L₀ := e.isSimpleGroup
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hf : Function.Injective σ := by
    have hk : σ.asGroupHom.ker = ⊥ := by
      obtain hb | ht := IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.asGroupHom.ker inferInstance
      · exact hb
      have hfix : subspaceCommutator ρ ⊤ L ≤ fixedSpace ρ L := by
        intro v hv l
        let l₀ : L₀ := ⟨⟨l,L.le_normalizer l.property⟩,l.property⟩
        have hl : σ.asGroupHom l₀ = 1 := by
          change l₀ ∈ σ.asGroupHom.ker
          rw [ht]
          trivial
        exact congrArg (fun a => ((a.val (⟨v,hv⟩ : subspaceCommutator ρ ⊤ L) : subspaceCommutator ρ ⊤ L) : V)) hl
      have htop := le_fixedSpace_of_commutator_le_fixedSpace ρ L ⊤
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hfix
      have hz : subspaceCommutator ρ ⊤ L = ⊥ := (subspaceCommutator_eq_bot_iff ρ ⊤ L).mpr htop
      have hc := hd
      rw [hz, finrank_bot] at hc
      omega
    intro x y hxy
    exact (σ.asGroupHom.ker_eq_bot_iff.mp hk) (Units.ext hxy)
  obtain ⟨eg,f,hf⟩ := BinaryFullLinearRecognition.exists_natural_equiv σ hf e hd
  exact ⟨eg,f,hf⟩
end Representation.BinaryFullLinearRecognition
