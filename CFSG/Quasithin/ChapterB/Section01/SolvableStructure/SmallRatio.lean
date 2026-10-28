module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# A small ratio from a solvable dual FF action

For a faithful binary representation of a finite solvable group with trivial
two-core, the solvable FF theorem applied to the actual dual constructs its
internal S₃ factors and their natural two-dimensional supports. A Sylow
involution in one factor displaces the dual into that factor's support.
Contragredience preserves the displacement of this same involution, giving
quadratic ratio at most two on the original module, and hence cubic ratio
at most two.

This is the solvable specialization of the B.5.13 step used in
Aschbacher–Smith 15.4.2(4), printed p.1156. It uses the proved B.1.8 factor
construction and no nonsolvable FF classification.
-/

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableDualFF
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

omit [Finite D] in
private theorem dual_injective (hf : Function.Injective ρ) :
    Function.Injective ρ.dual := by
  intro g h he
  apply inv_injective
  apply hf
  ext v
  apply Module.eval_apply_injective (ZMod 2)
  ext f
  exact congrArg (fun T : Module.End (ZMod 2) (Module.Dual (ZMod 2) V) => T f v) he

/-- The actual dual FF action of a solvable group supplies a quadratic
actor with ratio at most two on the original module. -/
public theorem quadraticRatio_le_two
    (hs : Group.IsSolvable D) (hc : pCore 2 D = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ.dual) :
    quadraticRatio ρ ≤ 2 := by
  classical
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ.dual hs hc (dual_injective ρ hf) hff
  let i : Fin d.count := ⟨0, d.count_pos⟩
  let S : Sylow 2 (d.factor i) := Classical.choice inferInstance
  obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (d.toSolvableFFFactors.factorSylow_ne_bot i S)
  have ht2 : (t : D) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    rw [d.toSolvableFFFactors.factorSylow_card i S] at hh
    exact congrArg Subtype.val hh
  have ht1 : (t : D) ≠ 1 := fun he => ht (Subtype.ext he)
  have ho : orderOf (t : D) = 2 := orderOf_eq_prime ht2 ht1
  have hbound : fixedCodim ρ (zpowers (t : D)) ≤ 2 := by
    rw [← fixedCodim_zpowers_dual ρ (t : D), fixedCodim_zpowers_eq_displacement_rank]
    have hle : LinearMap.range (ρ.dual (t : D) - LinearMap.id) ≤
        subspaceCommutator ρ.dual ⊤ (d.factor i) := by
      rintro v ⟨w, rfl⟩
      exact Submodule.subset_span
        ⟨t, d.toSolvableFFFactors.factorSylow_le i S t.property,
          w, Submodule.mem_top, rfl⟩
    exact (Submodule.finrank_mono hle).trans_eq
      (d.toSolvableFFFactors.support_finrank i)
  obtain ⟨hA, hr, hq, _⟩ := involution_actor_rank_and_fixedCodim ρ (t : D) ho
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨zpowers (t : D), hA, hq, ?_⟩
  simpa only [hr, mul_one] using hbound

/-- The same original action has cubic ratio at most two. -/
public theorem cubicRatio_le_two
    (hs : Group.IsSolvable D) (hc : pCore 2 D = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ.dual) :
    cubicRatio ρ ≤ 2 :=
  (cubicRatio_le_quadraticRatio ρ).trans (quadraticRatio_le_two ρ hs hc hf hff)

end CFSG.Quasithin.ChapterB.SolvableDualFF
