module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Centralizing
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Residual
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.LinearQuotient
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.FaithfulAction
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.OppositeMarking

/-!
# The cover action in the graph-field branch

The earlier involution table and 16.4.8 placement identify the opposite
graph-field action and the common residual. Intrinsic models then supply
transvections with different centers on the same E. Compatible Sylow
placement and Frattini transfer prove transitivity of the actual Y and
the embedded residual-intersection identity, with relative normality.

In the centralizing alternative we construct an independent three-element
and apply quasithinness. The other alternative uses the exact kernel of
the action on the E₉ residual: the actual quotient M/E embeds in GL₂(3).
Quaternion uniqueness already holds in every subgroup of GL₂(3), forcing
normality incompatible with the transvection action. This stronger form
removes the need for the source's separate surjectivity calculation.

The final theorem completes the nontrivial-cover contradiction on the
prepared choices constructed by Geometry. The earlier table, E₉ residual,
16.4.8 placement and intrinsic model constructors remain explicit inputs.
Their discharge and the final graph-field assembly belong to the parent.
The original terminal helper remains available with its public interface.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed p.1191.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R J : Subgroup G}

/-- Terminal assembly after the two action alternatives have been established.
The opposite model and the placement of Q must be constructed by the caller. -/
theorem deltaZero_nonempty_of_cover_action_alternatives
    (h : IntersectionSetup T z L g R) (hqt : IsQuasithin G)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)))
    (d : NormalizerData L r z) (c : CoverActionData d)
    (d' : NormalizerData J z r) (c' : CoverActionData d')
    (hQT : d.Q ≤ (T : Subgroup G))
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hcase : coverY T r z ≤ centralizer (residual L r : Set G) ∨
      CoverGeneralLinear T r z) : (deltaZero L).Nonempty := by
  have hE := fourGroup_elementary_card h hr hr2 hout
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have htrans := coverY_transitive_of_models hE.1 hE.2 hr1 hz1 hs d c d' c'
  rcases hcase with hfix | hGL
  · obtain ⟨x, hx, hx3, hxD, hxf⟩ := independent_three_of_coverY_centralizes
      d c hD h9 (inf_le_left.trans hQT) hE.2 hz1 htrans hfix
    exact (no_independent_centralizing_three h hqt hr hr2 hout hD h9
      (coverY_le_normalizer T r z hx) hx3 hxD hxf).elim
  · have hQM : d.Q ≤ coverOvergroup T r z :=
      (le_inf hQT d.normalizes_four).trans le_sup_left
    exact (cover_no_generalLinear h hr2 d c hQM htrans hGL).elim

/-- Assemble the paired models, compatible Sylow placement, Frattini
transitivity and embedded residual identity. The opposite marking follows
from the earlier table and placement through the EmptyCase detector.

The prepared saturation and transport premises are the outputs of
`exists_saturated_intersection` and `exists_compatible_conjugator` in Geometry.
The constructor for the opposite intrinsic model is applied only after its
actual graph-field marking has been proved. -/
theorem cover_geometry_of_nontrivial_core_prepared {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z) (hcore : pCore 2 L ≠ ⊥)
    (hmodel : IsL3FourGraphField L r)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hplace : residual L r ≤ L.conjBy g)
    (htable : Cover.OppositeMarking.OuterInvolutionTable (L.conjBy g))
    (hsat : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (oppositeModels : IsL3FourGraphField (L.conjBy g) z →
      ∃ d' : NormalizerData (L.conjBy g) z r, CoverActionData d') :
    ∃ d0 : NormalizerData L r z, CoverActionData d0 ∧
      d0.Q ≤ (T : Subgroup G) ∧ CoverTransitive T r z ∧
      normalizer (fourGroup r z : Set G) ≤ normalizer (residual L r : Set G) ∧
      residual L r = (pResidual 2 (coverComponentIntersection L r z)).map
        (coverComponentIntersection L r z).subtype ∧
      ((residual L r).subgroupOf (normalizer (fourGroup r z : Set G))).Normal := by
  obtain ⟨hopp, hres⟩ := Cover.OppositeMarking.opposite_graphField_and_residual
    h hsmall hempty hr hr2 hout hmodel h9 hplace htable
  obtain ⟨d', c'⟩ := oppositeModels hopp
  obtain ⟨_, _, d0, c0, _, _, hQT, _⟩ := exists_compatible_model_in_sylow_prepared
    hG h hsmall hempty hr hr2 hout hTC hcore hmodel hD h9 hsat d c
  have hE := fourGroup_elementary_card h hr hr2 hout
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hs := four_centralizer_sylow_of_empty h hsmall hempty hr hr2 hsat
  have ht := coverY_transitive_of_models hE.1 hE.2 hr1 hz1 hs d0 c0 d' c'
  exact ⟨d0, c0, hQT, ht, cover_normalization_prepared h hsmall hempty
    hr hr2 hout hTC hsat htransport d0 c0 d' c' hres⟩

/-- The nontrivial-cover branch of 16.4.9(2), conditional only on the
specified earlier source facts, Geometry's prepared choices and intrinsic
model witnesses. In particular normalization, model placement, transitivity,
faithfulness and both terminal contradictions are derived here.

The explicit earlier inputs are the E₉ statement of 16.1.4(5), the outer
PSL₃(4) rows of 16.1.4(4)–(6), and the 16.4.8 placement. The parent constructs
both intrinsic model witnesses and supplies the prepared source choices.
The faithful-image form of quaternion uniqueness eliminates the need to
assume or establish the stronger full GL₂(3) quotient identification. -/
theorem deltaZero_nonempty_of_nontrivial_cover_prepared {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z) (hcore : pCore 2 L ≠ ⊥)
    (hmodel : IsL3FourGraphField L r)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hplace : residual L r ≤ L.conjBy g)
    (htable : Cover.OppositeMarking.OuterInvolutionTable (L.conjBy g))
    (hsat : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (oppositeModels : IsL3FourGraphField (L.conjBy g) z →
      ∃ d' : NormalizerData (L.conjBy g) z r, CoverActionData d') :
    (deltaZero L).Nonempty := by
  by_contra hempty
  obtain ⟨d0, c0, hQT, htrans, hnorm, _, _⟩ := cover_geometry_of_nontrivial_core_prepared
    hG h hsmall hempty hr hr2 hout hTC hcore hmodel hD h9 hplace htable
    hsat htransport d c oppositeModels
  by_cases hfix : coverY T r z ≤ centralizer (residual L r : Set G)
  · have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
    obtain ⟨x, hx, hx3, hxD, hxf⟩ := independent_three_of_coverY_centralizes
      d0 c0 hD h9 (inf_le_left.trans hQT)
      (fourGroup_elementary_card h hr hr2 hout).2 hz1 htrans hfix
    exact no_independent_centralizing_three h hG.quasithin hr hr2 hout hD h9
      (coverY_le_normalizer T r z hx) hx3 hxD hxf
  · have hDN := (coverOvergroup_le_normalizer T r z).trans hnorm
    have hK := coverResidualAction_kernel_exact h hG.evenType hG.quasithin
      hr hr2 hout hTC d0 c0 hD h9 hQT hDN htrans
    have hQM : d0.Q ≤ coverOvergroup T r z :=
      (le_inf hQT d0.normalizes_four).trans le_sup_left
    exact cover_not_normal_of_transitive h hr2 d0 c0 hQM htrans
      (cover_normal_of_faithful_residual_action d0 hQM hD h9 hDN hK)


end CFSG.Quasithin.Chapter16.Intersections.GraphField
