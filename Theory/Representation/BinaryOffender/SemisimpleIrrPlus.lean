module
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Irr⁺ members in semisimple restrictions

An invariant complement to the global fixed space contains every full
commutator subspace. Hence an Irr⁺ member has no fixed vectors in a
semisimple restriction and is already irreducible before taking its central
quotient. This is the Clifford-theory reduction in F.9.18(3).
-/

public noncomputable section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : Subgroup G} {I : Submodule (ZMod 2) V}

/-- Full commutator generation excludes fixed vectors in a semisimple
restriction, even when the whole representation has fixed vectors. -/
theorem IsIrrPlus.inf_fixedSpace_eq_bot_of_semisimple
    (hI : IsIrrPlus ρ K I) [IsSemisimpleRepresentation (ρ.comp K.subtype)] :
    I ⊓ fixedSpace ρ K = ⊥ := by
  let F : Subrepresentation (ρ.comp K.subtype) :=
    ⟨fixedSpace ρ K, by
      intro k v hv
      change ρ k v ∈ fixedSpace ρ K
      have hk : ρ k v = v := hv k
      rw [hk]
      exact hv⟩
  obtain ⟨C, hC⟩ := exists_isCompl F
  have hs : K ≤ subspaceStabilizer ρ C.toSubmodule := by
    apply le_subspaceStabilizer
    intro k hk v hv
    exact C.apply_mem_toSubmodule ⟨k, hk⟩ hv
  have hle : I ≤ C.toSubmodule := by
    rw [← hI.choose_spec.1]
    apply subspaceCommutator_le_of_le_sup_fixedSpace ρ hs
    have he := congrArg Subrepresentation.toSubmodule hC.sup_eq_top
    change fixedSpace ρ K ⊔ C.toSubmodule = ⊤ at he
    rw [sup_comm, he]
    exact le_top
  apply le_bot_iff.mp
  have hd := congrArg Subrepresentation.toSubmodule hC.inf_eq_bot
  change fixedSpace ρ K ⊓ C.toSubmodule = ⊥ at hd
  exact (inf_le_inf hle le_rfl).trans_eq ((inf_comm _ _).trans hd)

/-- An Irr⁺ member of a semisimple restriction is an actual simple
subrepresentation, with the literal invariant-subspace action. -/
theorem IsIrrPlus.irreducible_of_semisimple
    (hI : IsIrrPlus ρ K I) [IsSemisimpleRepresentation (ρ.comp K.subtype)] :
    IsIrreducible (invariantSubspace ρ K I hI.choose).toRepresentation := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mpr
  refine ⟨?_, ?_⟩
  · intro h
    exact hI.ne_bot ρ (congrArg Subrepresentation.toSubmodule h)
  · intro J hJ
    have hs : K ≤ subspaceStabilizer ρ J.toSubmodule := by
      apply le_subspaceStabilizer
      intro k hk v hv
      exact J.apply_mem_toSubmodule ⟨k, hk⟩ hv
    rcases hI.eq_or_le_fixedSpace ρ hs hJ.le with he | hf
    · exact (hJ.ne (Subrepresentation.toSubmodule_injective he)).elim
    · apply Subrepresentation.toSubmodule_injective
      exact le_bot_iff.mp ((le_inf (show J.toSubmodule ≤ I from hJ.le) hf).trans_eq
        (hI.inf_fixedSpace_eq_bot_of_semisimple ρ))

end Representation.BinaryOffender
