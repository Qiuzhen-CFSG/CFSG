module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ModelInput
/-!
# Pure intersections in both summands of the original doubled orbit

The source pure-intersection premise names the natural summand only.
Lift the marked outer automizer to its actual ambient normalizer
representative. Conjugation by this representative transports each
intersection with a conjugate orbit, and preserves its noncentrality.
The natural-summand restriction therefore gives the dual restriction too.

This supplies the two-sided pure-intersection input in the first-stage
argument owned by qt-d-double-natural-weak-closure. The compatible model
and the offender contradictions are still obligations of that owner.
Source: Aschbacher--Smith,12.1.6(2) and12.1.8, printed pp.791--793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
variable {G : Type*} [Group G] {W : Subgroup G} [IsElementaryAbelian 2 W]

/-- Transport vanishing intersections along an actual ambient automizer. -/
theorem intersection_map_eq_bot
    (P Q : Submodule (ZMod 2) (Additive W))
    (t : Automizer W) (ht : P.map (automizerRepresentation W t) = Q)
    (hp : ∀ g : G, ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      P ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥)
    (g : G) (hg : ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    Q ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  obtain ⟨m, hm⟩ := t.property
  have hW : W.map (MulAut.conj (m : G)).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp m.property
  have hconj : (W.map (MulAut.conj ((m : G)⁻¹ * g)).toMonoidHom).map
      (MulAut.conj (m : G)).toMonoidHom = W.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply]
    group
  have hg' : ⁅W, W.map (MulAut.conj ((m : G)⁻¹ * g)).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map (MulAut.conj (m : G)).toMonoidHom) he
    rw [map_commutator, hW, hconj, Subgroup.map_bot] at hh
    exact hg hh
  apply bot_unique
  intro u hu
  change u = 0
  have huQ := hu.1
  rw [← ht] at huQ
  obtain ⟨v, hv, he⟩ := huQ
  have hvm : (v.toMul : G) ∈ W.map (MulAut.conj ((m : G)⁻¹ * g)).toMonoidHom := by
    have hu' := (mem_subgroupSpace W _ u).mp hu.2
    rw [← hconj] at hu'
    obtain ⟨z,hz,heq⟩ := hu'
    have hm' : (automizerRepresentation W t v).toMul.val =
        MulAut.conj (m : G) (v.toMul : G) := by
      change (t.val v.toMul : G) = _
      rw [← hm]
      rfl
    have he' := congrArg (fun w : Additive W => w.toMul.val) he
    rw [hm'] at he'
    have hzv : z = (v.toMul : G) := (MulAut.conj (m : G)).injective (heq.trans he'.symm)
    exact hzv ▸ hz
  have hv0 : v = 0 := by
    have hvI : v ∈ P ⊓ subgroupSpace W
        (W.map (MulAut.conj ((m : G)⁻¹ * g)).toMonoidHom) :=
      ⟨hv, (mem_subgroupSpace W _ v).mpr hvm⟩
    rw [hp _ hg'] at hvI
    exact hvI
  rw [← he, hv0, map_zero]

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The source's pure-natural premise also controls the original dual summand,
using the outer interchange of the compatible actual action. -/
theorem dual_intersection_eq_bot (M : B.MarkedAutomizerModel)
    (hp : B.PureIntersectionCentralizes) (g : G)
    (hg : ⁅componentOrbit V (T : Subgroup G),
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    B.dualSpace ⊓ subgroupSpace (componentOrbit V (T : Subgroup G))
      ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom) = ⊥ := by
  obtain ⟨t, _, ht⟩ := M.setup.outer
  rw [M.natural_eq, M.dual_eq, M.representation_eq] at ht
  exact WeakClosure.intersection_map_eq_bot _ _ t ht
    (fun k hk => B.natural_intersection_eq_bot hp k hk) g hg

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
