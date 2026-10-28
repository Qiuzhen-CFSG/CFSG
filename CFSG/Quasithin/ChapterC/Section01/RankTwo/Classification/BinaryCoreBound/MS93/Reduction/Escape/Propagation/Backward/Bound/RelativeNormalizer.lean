module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.RelativePencil

/-!
# The backward bound with source relative-normalizer generation

The generating subgroup in MS93 is `G_a ∩ N(Q_t)`. The critical-pair
selection and commutator bounds in `Bound.Commutator` do not use generation:
a failed W(t) bound produces a nontrivial critical commutator inside both
R₀ and the starting edge displacement. Since R₀ ∩ Z_a = R has order two,
this puts R in that displacement. The relative-normalizer noncontainment
proved in `Selection.Pencil.Choices.RelativePencil` gives the contradiction.

The existing radius/H identification supplies moving membership at the
vertex four before the endpoint. Together these prove `RelativeBoundFacts`
from the preceding stages, preserving the reverse moving condition in W(t)
and leaving the legacy `BoundFacts` API unchanged.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation on p.881 and (4.3.6), pp.886--887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The reverse-moving W(t) bound with the literal source generating group.
No edge-stabilizer generation or later product-normality result is assumed. -/
theorem noncentral_backward_bound_of_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (d t : Vertex R)
    (hd : Before p.a p.a' d 4) (hn : ¬ radiusCommutator p.a p.a' ≤ localCenter d)
    (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' =
      stabilizer R p.a) :
    backwardSpan geometry p.a t ≤ Q R d := by
  classical
  obtain ⟨hi⟩ := initial p
  by_contra hW
  obtain ⟨e, het, hea, f, hf, hfe, hcrit⟩ := exists_backward_critical p d t hd hW
  have hsmall := backward_critical_commutator_le_edge source p hb control d t e f hd hat het hea hfe
  have hZf : Z R f ≤ backwardSpan geometry p.a t :=
    (show Z R f ≤ V R e from le_iSup_of_le f (le_iSup_of_le hfe.le le_rfl)).trans
      (V_le_backwardSpan het hea)
  have hR : ⁅Z R f, Z R d⁆ ≤ radiusCommutator p.a p.a' := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZf).trans
      (noncentral_backward_commutator_le source p hb modules hi control edge rigidity d t hd hn)
  have hline : ⁅Z R f, Z R d⁆ ≤ criticalCommutator p.a p.a' := by
    rw [← radius_inf_start_Z source p hi]
    exact le_inf hR (hsmall.trans
      ((Initial.edge_le_natural source p.a t p.color_a hat).trans (U_le_Z p.a)))
  let := finite_stabilizer R p.a
  let : Finite (criticalCommutator p.a p.a') := Finite.of_injective
    (inclusion (p.critical_le_radius_inf_start.trans (inf_le_right.trans (Z_le_stabilizer R p.a))))
    (inclusion_injective _)
  let : Finite (⁅Z R f, Z R d⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hline) (inclusion_injective _)
  have hnontrivial : 1 < Nat.card (⁅Z R f, Z R d⁆ : Subgroup (FreeAmalgam R)) :=
    (one_lt_card_iff_ne_bot _).mpr (source.critical_noncommutation geometry f hf hcrit)
  have heq : ⁅Z R f, Z R d⁆ = criticalCommutator p.a p.a' :=
    eq_of_le_of_card_ge hline (by rw [hi.critical_card]; omega)
  exact Products.Selection.critical_not_le_generating_relativeNormalizer
    source p hb modules initial t hat hgen (heq ▸ hsmall)

/-- Source (4.3.6) with relative-normalizer generation, including moving
membership and the full reverse-moving span bound, from preceding stages. -/
theorem relativeBoundFacts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) : Products.Selection.RelativeBoundFacts geometry where
  bound p d hd hn := by
    obtain ⟨hi⟩ := initial p
    refine ⟨noncentral_backward_moving_of_radius_eq_H source p hb control edge rigidity d hd hn
      (Radius.radius_eq_H source p hb hi control), ?_⟩
    intro t hat hgen
    exact noncentral_backward_bound_of_relativeNormalizer
      source p hb modules initial control edge rigidity d t hd hn hat hgen

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
