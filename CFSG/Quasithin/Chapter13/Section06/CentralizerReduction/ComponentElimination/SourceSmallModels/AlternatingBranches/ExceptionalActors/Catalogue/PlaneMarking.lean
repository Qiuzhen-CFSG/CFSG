module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking.Bounds
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking.Placement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking.Actions

/-!
# Intrinsic marking of the exceptional A₇ plane stabilizer

A faithful binary four-space has plane stabilizers of order 72. The given
Sylow subgroup supplies the literal four-plus-three permutation marking.
In these coordinates, the cyclic and natural actors fully move the plane;
exactly one diagonal does so and the other fixes it pointwise. The choice
uses the given representation and plane.

For a permitted source actor, pullback along the same relabelling lies in
the marked block. Its full-commutator hypothesis excludes the inactive
diagonal. Four-candidate exhaustion and construction from the ambient source
configuration remain separate results; neither is a premise here.

Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
namespace Catalogue.PlaneMarking
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- A permutation of the seven letters identifies the actual plane stabilizer
and gives the two possible active-diagonal markings explicitly. -/
theorem exists_marked_plane (ρ : Representation (ZMod 2) A7 W)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) W = 4)
    (P : Submodule (ZMod 2) W) (hP : Module.finrank (ZMod 2) P = 2)
    (S : Sylow 2 A7) (hS : (S : Subgroup A7) ≤ subspaceStabilizer ρ P) :
    ∃ g : Equiv.Perm (Fin 7),
      subspaceStabilizer ρ P = blockStabilizer.map (relabelling g).toMonoidHom ∧
      subspaceCommutator ρ P (cyclicActor.map (relabelling g).toMonoidHom) = P ∧
      subspaceCommutator ρ P (naturalActor.map (relabelling g).toMonoidHom) = P ∧
      ((subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = P ∧
        subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = ⊥) ∨
       (subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = P ∧
        subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = ⊥)) := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := W) (by omega : 0 < Module.finrank (ZMod 2) W)
  obtain ⟨g, hg⟩ := exists_block_marking_of_card (subspaceStabilizer ρ P)
    (planeStabilizer_card_index ρ hρ hdim P hP).1 S hS
  exact ⟨g, hg, candidate_commutators ρ P hρ hdim hP g hg.ge⟩

end Catalogue.PlaneMarking

open Catalogue Catalogue.PlaneMarking
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A7 W} {P : Submodule (ZMod 2) W}
  {S : Sylow 2 A7} {D : Subgroup A7}

/-- The literal `PermittedActor` contract pulls back to the marked block,
and its full-commutator clause rules out the inactive diagonal. -/
theorem PermittedActor.marked_alternatives (h : PermittedActor ρ P S D)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) W = 4)
    (hP : Module.finrank (ZMod 2) P = 2) :
    ∃ g : Equiv.Perm (Fin 7),
      subspaceStabilizer ρ P = blockStabilizer.map (relabelling g).toMonoidHom ∧
      D.comap (relabelling g).toMonoidHom ≤ blockStabilizer ∧
      subspaceCommutator ρ P (cyclicActor.map (relabelling g).toMonoidHom) = P ∧
      subspaceCommutator ρ P (naturalActor.map (relabelling g).toMonoidHom) = P ∧
      ((subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = P ∧
        subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = ⊥ ∧
        D ≠ diagonalMinus.map (relabelling g).toMonoidHom) ∨
       (subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = P ∧
        subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = ⊥ ∧
        D ≠ diagonalPlus.map (relabelling g).toMonoidHom)) := by
  obtain ⟨g, hg, hc, hn, hd⟩ := exists_marked_plane ρ hρ hdim P hP S h.sylow_stabilizes
  have hle : D.comap (relabelling g).toMonoidHom ≤ blockStabilizer := by
    intro a ha
    have hm := h.stabilizes ha
    rw [hg, Subgroup.mem_map_equiv] at hm
    simpa using hm
  have hne (I : Subgroup A7) (hI : subspaceCommutator ρ P I = ⊥) : D ≠ I := by
    intro he
    have hpbot : P = ⊥ := h.commutator_eq.symm.trans (by simpa only [he] using hI)
    rw [hpbot, finrank_bot] at hP
    omega
  refine ⟨g, hg, hle, hc, hn, ?_⟩
  rcases hd with ⟨hp, hm⟩ | ⟨hm, hp⟩
  · exact Or.inl ⟨hp, hm, hne _ hm⟩
  · exact Or.inr ⟨hm, hp, hne _ hp⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
