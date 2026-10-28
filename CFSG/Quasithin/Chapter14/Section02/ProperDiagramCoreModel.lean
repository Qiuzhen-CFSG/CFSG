module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCoreActor
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramModelPair
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramHallFixer
/-!
# The diagram exception from the original maximal two-core

The maximal two-core fixes the marked Borel quotient by commutators.
The full-torus automorphism theorems therefore force such an actor to
normalize the chosen parabolic residual in the symplectic case. In the
linear case failure to normalize forces field order four. The proofs
retain the actual source action and the literal selected residual.

Source: Aschbacher--Smith 14.2.12, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

theorem linear_core_actor_normalizes_or_four
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap M K).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F)
    (hF : Nat.card F = 2^f) (hf : 1 < f)
    (g : H) (hg : g ∈ M.pCoreIn 2) :
    g ∈ normalizer (markedParabolicResidual M K e
      (Matrix.PSL3.LinearThree.pointParabolic F) : Set H) ∨ f = 2 := by
  let a := markedParabolicActor M K e g
  have hB := markedParabolicActor_borel M K e he g (pCoreIn_le 2 M hg)
  have hfix (b : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (hb : b ∈ Matrix.PSL3.CartanActions.torus F) :
      a b * b⁻¹ ∈ Matrix.PSL3.LinearThree.unipotent F := by
    have hh := markedParabolicActor_core_displacement M K e he g hg b
      (Matrix.PSL3.CartanActions.torus_le_borel F hb)
    rwa [pCoreIn,Matrix.PSL3.CartanActions.BorelQuotient.twoCore_eq F hF,
      map_subgroupOf_eq_of_le (Matrix.PSL3.LinearThree.unipotent_le_borel F)] at hh
  by_cases hn : g ∈ normalizer (markedParabolicResidual M K e
      (Matrix.PSL3.LinearThree.pointParabolic F) : Set H)
  · exact Or.inl hn
  right
  apply Matrix.PSL3.CartanActions.FullTorusFixer.degree_eq_two_of_fixed_torus hF hf a hB hfix
  rintro ⟨⟨u,hu⟩,_⟩
  apply hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply markedParabolicResidual_conj M K e
    (Matrix.PSL3.LinearThree.pointParabolic F) (Matrix.PSL3.LinearThree.pointParabolic F) g
  rcases Matrix.PSL3.LinearThree.point_parabolic_map_pair_of_borel F a hB with h | h
  · exact h
  · exact (Matrix.PSL3.LinearThree.OuterExtensions.pointParabolic_not_conjugate_line
      F (by omega) hF u (hu.symm.trans h)).elim

theorem symplectic_core_actor_normalizes
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (he : (componentOverlap M K).map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel)
    (hF : Nat.card F = 2^f) (hf : 1 < f)
    (g : H) (hg : g ∈ M.pCoreIn 2) :
    g ∈ normalizer (markedParabolicResidual M K e
      (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)) : Set H) := by
  let a := markedParabolicActor M K e g
  have hB := markedParabolicActor_borel M K e he g (pCoreIn_le 2 M hg)
  have hd := Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer.preservesDiagram_of_fixed_torus
    hF hf a hB (by
      intro x
      let b := Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.torusSection x
      let c : Theory.SpecificGroups.SymplecticFour.borel (F := F) :=
        ⟨a b.val,hB.le (mem_map_of_mem _ b.property)⟩
      have hh := markedParabolicActor_core_displacement M K e he g hg b.val b.property
      rw [Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.borel_twoCoreIn hF] at hh
      have hk : c * b⁻¹ ∈ Theory.SpecificGroups.SymplecticFour.borelCharacters.ker := by
        rw [Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.characters_ker]
        exact hh
      have hz := MonoidHom.mem_ker.mp hk
      rw [map_mul,map_inv,mul_inv_eq_one] at hz
      exact hz.trans (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.characters_torusSection x))
  have hp := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.parabolic_pair_map_of_unipotent_map
    hF hf a hd
    (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer.map_unipotent_of_map_borel hF a hB)
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact markedParabolicResidual_conj M K e _ _ g hp.1
end CFSG.Quasithin.Chapter14.Section02
