module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.VectorStabilizers.Inner
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure

/-!
# The pure-vector family of H.9.1(3)

For the specified action of the actual automorphism group in degrees four
and five, the pure-vector stabilizer equals its embedded two-residual.
Its intrinsic two-core is the elementary line radical, the quotient is
GL_(n−1)(2), and the extension splits. Its natural commutator space is X
and its dual commutator space is the hyperplane ann(x). The quotient
acts as the full linear group on that hyperplane, compatibly with X/span(x).

For every given Sylow T, the actual natural-summand normalizer T₁ fixes
one line; any nonzero vector of that line has T-centralizer T₁, which
is Sylow in its full stabilizer. All these conclusions follow from the
coordinate action, the dimension, and the supplied Sylow subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(3),
printed pp.389–390. This clause is unchanged by the correction to (4).
-/

public section
namespace CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

/-- The pure-vector group and module conclusions, with the actual radical and quotient. -/
theorem pure_stabilizer_structure {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} (hx : x ≠ 0) :
    fullStabilizer d (x,0) = innerResidual d (x,0) ∧
    (pCore 2 (fullStabilizer d (x,0))).map (fullStabilizer d (x,0)).subtype =
      Pure.embeddedRadical d x ∧
    IsElementaryAbelian 2 (Pure.embeddedRadical d x) ∧
    Nat.card (Pure.embeddedRadical d x) = 2 ^ (n - 1) ∧
    Nonempty ((fullStabilizer d (x,0) ⧸ pCore 2 (fullStabilizer d (x,0))) ≃*
      LinearGroup (n - 1)) ∧
    Nonempty (SemidirectProduct (Pure.innerRadical d x)
      (BinaryLinear.GL (Pure.pointQuotient x)) (Pure.splitAction d hx) ≃*
        fullStabilizer d (x,0)) ∧
    Representation.Coinvariants.ker (Pure.innerNaturalRepresentation d x) = ⊤ ∧
    Representation.Coinvariants.ker (Pure.innerDualRepresentation d x) = annihilator x ∧
    Module.finrank (ZMod 2) (annihilator x) = n - 1 :=
  ⟨Pure.fullStabilizer_eq_innerResidual hn d hx, Pure.full_twoCore_map hn d hx,
    Pure.embeddedRadical_elementary d x, Pure.embeddedRadical_card d hx,
    ⟨Pure.fullQuotientTwoCoreEquivLinear hn d hx⟩, ⟨Pure.fullSemidirectEquiv hn d hx⟩,
    Pure.inner_natural_commutator hn d hx, Pure.inner_dual_commutator d hx,
    Pure.annihilator_finrank hx⟩

/-- The quotient equivalence is the original action on the annihilator hyperplane. -/
theorem pure_annihilator_quotient_action {n : ℕ} (d : CoordinateAction n)
    (x : BinaryLinear.OuterCyclic.Space n) :
    Function.Surjective (Pure.innerAnnihilatorAction d x) ∧
    (∀ a : innerStabilizer d (x,0),
      Pure.innerQuotientEquivAnnihilator d x (QuotientGroup.mk' _ a) =
        Pure.innerAnnihilatorAction d x a) ∧
    (∀ (a : innerStabilizer d (x,0)) (q : annihilator x),
      d.representation a.val (0,q.val) = (0,(Pure.innerAnnihilatorAction d x a q).val)) :=
  ⟨Pure.innerAnnihilatorAction_surjective d x, Pure.innerQuotientEquivAnnihilator_mk d x,
    Pure.inner_annihilator_action d x⟩

/-- The original, fixed-Sylow marking in H.9.1(3), for every nonzero generator. -/
theorem pure_sylow_marking {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (LinearGroup n))) :
    Module.finrank (ZMod 2) (Pure.naturalFixedSpace d (Pure.sylowSummandNormalizer d T)) = 1 ∧
    ∀ x : BinaryLinear.OuterCyclic.Space n, x ≠ 0 →
      x ∈ Pure.naturalFixedSpace d (Pure.sylowSummandNormalizer d T) →
      (T : Subgroup (MulAut (LinearGroup n))) ⊓ fullStabilizer d (x,0) =
        Pure.sylowSummandNormalizer d T ∧
      ∃ P : Sylow 2 (fullStabilizer d (x,0)),
        (P : Subgroup (fullStabilizer d (x,0))).map (fullStabilizer d (x,0)).subtype =
          Pure.sylowSummandNormalizer d T := by
  refine ⟨Pure.sylow_fixed_finrank hn d T, ?_⟩
  intro x hx hfixed
  exact ⟨Pure.sylow_centralizer_eq hn d T hx hfixed,
    Pure.sylow_centralizer_isSylow hn d T hx hfixed⟩

end CFSG.Quasithin.ChapterH.NaturalDual
