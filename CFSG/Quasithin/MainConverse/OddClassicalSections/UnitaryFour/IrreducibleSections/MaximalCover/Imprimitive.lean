module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Geometry
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Monomial
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Pullback
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Imprimitive.Blocks
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Geometry

/-!
# Imprimitive PSU₄(3) subgroups: reduction to subspace stabilizers

Irreducibility leaves four lines or two planes. The four lines give a basis
and the existing monomial theorem. For two planes the block permutation
kernel fixes each plane. Its inclusion in the full preimage of a projective
plane stabilizer retains the entire scalar kernel. The permutation quotient
is solvable, and its kernel is normal in the full SU preimage.

The plane stabilizer calculation splits by its restricted Hermitian radical.
Nondegenerate planes use the solvable coordinate-plane stabilizer and actual
coordinate transport. A nonzero radical, including a totally isotropic plane,
uses the isotropic stabilizer calculation; an actual quotient model A₆ maps
into S₇ through its six-letter permutation representation.

The assembly remains conditional on the separately owned isotropic stabilizer,
nondegenerate transport, and coordinate-plane solvability theorems. These
premises must be discharged before obtaining the unconditional imprimitive
branch. No hypothesis of maximality or simplicity is needed for the reduction.

Source: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4 and 482
of `refs/quasithin.pdf`; GLS3, §2.7 for the Hermitian and scalar conventions.
-/

public noncomputable section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
open Module

private theorem kernelModel_of_injective {G H : Type} [Group G] [Group H]
    (h : HasSolvableKernelModel H) (f : G →* H) (hf : Function.Injective f) :
    HasSolvableKernelModel G := by
  let : Group.IsSolvable f.ker := by
    rw [f.ker_eq_bot_iff.mpr hf]
    infer_instance
  exact h.pullback f

private theorem kernelModel_of_alternatingSix {G : Type} [Group G]
    (m : Group.SolvableKernelModel G (alternatingGroup (Fin 6))) :
    HasSolvableKernelModel G := by
  let := m.normal
  let := m.solvable
  let e := (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (show 6 ≤ 7 by decide))).comp
    (alternatingGroup (Fin 6)).subtype
  have he : Function.Injective e :=
    (Equiv.Perm.viaEmbeddingHom_injective _).comp Subtype.val_injective
  refine Or.inl ⟨e.comp (m.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' m.kernel)), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ e he,
    MonoidHom.ker_comp_of_injective _ m.quotientEquiv.toMonoidHom m.quotientEquiv.injective,
    QuotientGroup.ker_mk']
  exact m.solvable

/-- A two-plane stabilizer has a concrete kernel model, given the actual
isotropic-stabilizer calculation and solvability of nondegenerate plane
stabilizers. A nonzero radical handles every degenerate restriction. -/
theorem plane_stabilizer_hasSolvableKernelModel_of_stabilizers
    (hisotropic : ∀ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ → W ≠ ⊤ →
      W ≤ orthogonal W → Group.IsSolvable (projectiveStabilizer W) ∨
        Nonempty (Group.SolvableKernelModel (projectiveStabilizer W)
          (alternatingGroup (Fin 6))))
    (hnondegenerate : ∀ W : Submodule FiniteField.Nine (Space 4),
      radical W = ⊥ → finrank FiniteField.Nine W = 2 →
        Group.IsSolvable (projectiveStabilizer W))
    (W : Submodule FiniteField.Nine (Space 4)) (hd : finrank FiniteField.Nine W = 2) :
    HasSolvableKernelModel (projectiveStabilizer W) := by
  by_cases hr : radical W = ⊥
  · let := hnondegenerate W hr hd
    exact HasSolvableKernelModel.of_solvable _
  have htop : W ≠ ⊤ := by
    intro h
    have hh : finrank FiniteField.Nine W = 4 := by
      rw [h, finrank_top]
      exact Module.finrank_pi _
    omega
  have hrtop : radical W ≠ ⊤ := by
    intro ht
    exact htop (top_unique (ht ▸ (inf_le_left : radical W ≤ W)))
  have hm : HasSolvableKernelModel (projectiveStabilizer (radical W)) := by
    rcases hisotropic (radical W) hr hrtop (radical_totallyIsotropic W) with hs | hm
    · let := hs
      exact HasSolvableKernelModel.of_solvable _
    · obtain ⟨m⟩ := hm
      exact kernelModel_of_alternatingSix m
  exact kernelModel_of_injective hm
    (Subgroup.inclusion (projectiveStabilizer_le_radical W))
    (Subgroup.inclusion_injective _)

namespace ImprimitivitySystem
variable {U : Subgroup (Carrier 4)} {r : ℕ} (B : ImprimitivitySystem U r)

/-- Every element of the permutation kernel fixes each summand setwise. -/
theorem kernel_map_summand (g : B.permutationHom.ker) (i : Fin r) :
    (B.summand i).map (liftedRepresentation U g.val) = B.summand i := by
  rw [B.map_summand, show B.permutationHom g.val = 1 from g.property]
  rfl

/-- The block kernel lies in the full preimage of each actual projective
subspace stabilizer. All scalars are retained in the target. -/
@[expose] def kernelToStabilizer (i : Fin r) :
    B.permutationHom.ker →* fullPreimage (projectiveStabilizer (B.summand i)) where
  toFun g := ⟨g.val.val, by
    change project 4 g.val.val ∈ projectiveStabilizer (B.summand i)
    apply Subgroup.mem_map.mpr
    refine ⟨g.val.val, ?_, rfl⟩
    rw [mem_specialStabilizer_iff]
    intro v
    change liftedRepresentation U g.val v ∈ B.summand i ↔ v ∈ B.summand i
    constructor
    · intro hv
      rw [← B.kernel_map_summand g i] at hv
      obtain ⟨w, hw, he⟩ := hv
      have : w = v := ((liftedRepresentation U).apply_bijective g.val).injective he
      exact this ▸ hw
    · intro hv
      rw [← B.kernel_map_summand g i]
      exact Submodule.mem_map_of_mem hv⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem kernelToStabilizer_injective (i : Fin r) :
    Function.Injective (B.kernelToStabilizer i) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : fullPreimage (projectiveStabilizer (B.summand i)) => z.val) h

/-- A kernel model for one block stabilizer suffices: its pullback models
the block kernel, while the permutation quotient gives the solvable outer layer. -/
theorem hasSolvableLayersModel_of_stabilizer (i : Fin r)
    (h : HasSolvableKernelModel (projectiveStabilizer (B.summand i))) :
    HasSolvableLayersModel (fullPreimage U) := by
  have hm := fullPreimage_hasSolvableKernelModel_of_projective
    (projectiveStabilizer (B.summand i)) h
  exact .normal B.permutationHom.ker B.permutationQuotient_isSolvable
    (kernelModel_of_injective hm (B.kernelToStabilizer i)
      (B.kernelToStabilizer_injective i))

end ImprimitivitySystem

/-- Conditional imprimitive assembly. It does not require maximality or
simplicity, but the two stated stabilizer calculations remain obligations. -/
theorem IsImprimitive.hasSolvableLayersModel_of_stabilizers
    (hisotropic : ∀ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ → W ≠ ⊤ →
      W ≤ orthogonal W → Group.IsSolvable (projectiveStabilizer W) ∨
        Nonempty (Group.SolvableKernelModel (projectiveStabilizer W)
          (alternatingGroup (Fin 6))))
    (hnondegenerate : ∀ W : Submodule FiniteField.Nine (Space 4),
      radical W = ⊥ → finrank FiniteField.Nine W = 2 →
        Group.IsSolvable (projectiveStabilizer W))
    {U : Subgroup (Carrier 4)} (h : IsImprimitive U) (hred : ¬ IsReducible U) :
    HasSolvableLayersModel (fullPreimage U) := by
  rcases h.monomial_or_two_planes hred with hm | ⟨B, hd⟩
  · exact .direct (hm.hasSolvableKernelModel U)
  · exact B.hasSolvableLayersModel_of_stabilizer 0
      (plane_stabilizer_hasSolvableKernelModel_of_stabilizers
        hisotropic hnondegenerate (B.summand 0) (hd 0))

/-- Only the dimension-two part of nondegenerate coordinate transport is
needed here; there is no dependency on the PSU₃(3) line-stabilizer model. -/
theorem IsImprimitive.hasSolvableLayersModel_of_coordinate_stabilizers
    (hisotropic : ∀ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ → W ≠ ⊤ →
      W ≤ orthogonal W → Group.IsSolvable (projectiveStabilizer W) ∨
        Nonempty (Group.SolvableKernelModel (projectiveStabilizer W)
          (alternatingGroup (Fin 6))))
    (htransport : ∀ W : Submodule FiniteField.Nine (Space 4),
      radical W = ⊥ → finrank FiniteField.Nine W = 2 →
        Nonempty (projectiveStabilizer W ≃*
          projectiveStabilizer (NondegenerateStabilizers.coordinateSubspace 2)))
    (hplane : Group.IsSolvable
      (projectiveStabilizer (NondegenerateStabilizers.coordinateSubspace 2)))
    {U : Subgroup (Carrier 4)} (h : IsImprimitive U) (hred : ¬ IsReducible U) :
    HasSolvableLayersModel (fullPreimage U) := by
  apply h.hasSolvableLayersModel_of_stabilizers hisotropic _ hred
  intro W hr hd
  obtain ⟨e⟩ := htransport W hr hd
  let := hplane
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
