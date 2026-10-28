module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField.Kernel
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The nonbinary symplectic torus kernel

The actual Borel character map detects the displacement of an automorphism
stabilizing its unipotent Sylow subgroup. Trivial displacement forces a trivial
torus action. The exceptional graph map acts by (x,y) ↦ (y,x²), so the proved
graph-power calculation, together with the diagram-preserving semilinear
classification, detects precisely the inner actors. Conjugation transports this
calculation to every Sylow marking. Perfectness supplies the actual equivalence
from the nonbinary derived carrier to the full matrix group.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, B.4.2(3), B.5.6, and printed
p.1144, proof of 15.3.49(k). No restriction to diagram-preserving actors or
assumption that the graph automorphism has order two is made here.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The full Sylow-normalizer quotient detects every outer symplectic actor. -/
theorem symplectic_torusRigid {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    TorusRigid (Sp F) := by
  intro P a hP ha
  let aP : stabilizerAt P := ⟨a, hP⟩
  let e := alignment hF hn.le P
  let b := alignActorHom hF hn.le P aP
  have heU : unipotent.map e.toMonoidHom = (P : Subgroup (Sp F)) :=
    alignment_unipotent hF hn.le P
  have heB : borel.map e.toMonoidHom = normalizer (P : Set (Sp F)) := by
    rw [borel_eq_normalizer_unipotent, map_equiv_normalizer_eq, heU]
    rfl
  have htorus : torusAction hF b = 1 := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := characters_surjective z
    rw [torusAction_characters]
    have hx := ha (e x) (heB.le (mem_map_of_mem e.toMonoidHom x.property))
    have hm : (x⁻¹ * borelAction b x).val ∈ unipotent (F := F) := by
      apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
      rw [heU]
      change e (x.val⁻¹ * e.symm (a (e x.val))) ∈ (P : Subgroup (Sp F))
      rw [map_mul, map_inv, e.apply_symm_apply]
      exact hx
    have hc := (borelCharacters_eq_one (x⁻¹ * borelAction b x)).mpr hm
    rw [map_mul, map_inv, inv_mul_eq_one] at hc
    exact hc.symm
  apply (torusActionAt_eq_one_iff_inner hF hn
    DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram P aP).mp
  exact htorus

omit [CharP F 2] in
/-- Perfectness identifies the nonbinary derived carrier with the actual full group. -/
theorem derived_symplectic_torusRigid {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    TorusRigid (commutator (Matrix.symplecticGroup (Fin 2) F)) := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact (symplectic_torusRigid hF hn).of_equiv (derivedEquivFull_of_card_gt_two hq)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField
