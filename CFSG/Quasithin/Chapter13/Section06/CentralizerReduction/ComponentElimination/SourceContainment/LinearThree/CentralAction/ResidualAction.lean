module

public import Theory.Representation.PSL3Two.DoubledParabolic.Residual
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceDoubledNatural

/-!
# Transport of the doubled-natural residual obstruction

The full normalizer P maps onto the line parabolic, but only O²(P) must
normalize the split-point subgroup. Surjectivity on residuals supplies the
cubic actor used by the concrete model obstruction. This keeps P distinct
from O²(P) and never assumes that the latter surjects onto S₄.

The final lemma applies to the literal subgroup [V,L_v]. The actual
normalizer and module are supplied in `CentralAction.Normalizer`; their
parabolic image and split-point description remain source obligations.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation BinaryLinearThree BinaryLinearThree.DoubledParabolic
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
open ComponentSelection

/-- Only the two-residual of the source normalizer has to preserve Q. -/
theorem not_residual_normalizes_splitPlane
    {G : Type*} [_root_.Group G] [Finite G] (P U Q : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G))
    (π : P →* Matrix.PSL3Two.lineParabolicSL) (hπ : Function.Surjective π)
    (e : U ≃* Multiplicative (Vector × Vector))
    (he : ∀ p : P, ∀ u : U,
      e (conjugationAction U P hPU p u) = Multiplicative.ofAdd
        ((W.prod W) (π p : Group) (Multiplicative.toAdd (e u))))
    (x y : Vector) (hx : x 2 = 0) (hn : x ≠ 0)
    (hQ : (Q.subgroupOf U).map e.toMonoidHom =
      (splitPlane x y).toAddSubgroup.toSubgroup) :
    ¬ (pResidual 2 P).map P.subtype ≤ normalizer (Q : Set G) := by
  intro hPQ
  apply splitPlane_not_invariant_residual x y hx hn
  intro g hg w hw
  obtain ⟨c, hc, rfl⟩ := hg
  have hc' : c ∈ (pResidual 2 P).map π := by
    rwa [map_pResidual_of_surjective 2 π hπ]
  obtain ⟨p, hp, hpc⟩ := hc'
  let u : U := e.symm (Multiplicative.ofAdd w)
  have hu : e u ∈ (Q.subgroupOf U).map e.toMonoidHom := by
    rw [hQ]
    change Multiplicative.toAdd (e u) ∈ splitPlane x y
    simpa [u] using hw
  obtain ⟨q, hq, heq⟩ := hu
  have hqu : q = u := e.injective heq
  have huQ : (u : G) ∈ Q := hqu ▸ hq
  have hcQ : conjugationAction U P hPU p u ∈ Q.subgroupOf U :=
    (mem_normalizer_iff.mp (hPQ (mem_map_of_mem P.subtype hp)) (u : G)).mp huQ
  have hm : e (conjugationAction U P hPU p u) ∈
      (splitPlane x y).toAddSubgroup.toSubgroup := by
    rw [← hQ]
    exact mem_map.mpr ⟨_, hcQ, rfl⟩
  rw [he] at hm
  change (W.prod W) (π p : Group) (Multiplicative.toAdd (e u)) ∈ splitPlane x y at hm
  simpa [u, hpc] using hm

/-- Residual version of Source.doubled_natural_commutator_contradiction. -/
theorem doubled_natural_residual_commutator_contradiction
    {G : Type*} [_root_.Group G] [Finite G] (L V P U : Subgroup G) (v : G)
    (hPU : P ≤ normalizer (U : Set G))
    (π : P →* Matrix.PSL3Two.lineParabolicSL) (hπ : Function.Surjective π)
    (e : U ≃* Multiplicative (Vector × Vector))
    (he : ∀ p : P, ∀ u : U,
      e (conjugationAction U P hPU p u) = Multiplicative.ofAdd
        ((W.prod W) (π p : Group) (Multiplicative.toAdd (e u))))
    (x y : Vector) (hx : x 2 = 0) (hn : x ≠ 0)
    (hQ : ((⁅V, Lv L v⁆ : Subgroup G).subgroupOf U).map e.toMonoidHom =
      (splitPlane x y).toAddSubgroup.toSubgroup)
    (hPV : P ≤ normalizer (V : Set G))
    (hPL : (pResidual 2 P).map P.subtype ≤ normalizer (Lv L v : Set G)) : False := by
  apply not_residual_normalizes_splitPlane P U ⁅V, Lv L v⁆ hPU π hπ e he x y hx hn hQ
  intro p hp
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hPV (map_subtype_le _ hp)),
    mem_normalizer_iff_map_conj_eq.mp (hPL hp)]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
