module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SelectedEndpoint
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.Selection
public import Theory.Representation.BinaryOffender.CubicConjugateDimension

/-!
# Selected terminal endpoint geometry

The original F.9 construction and its genuine reversal select a critical
pair with positive denominator rank bounded by actor rank. The Chapter 13
bridge retains its literal conjugator, two-core denominators and quotient
action. The non-FF inequality makes the denominator commutator equal the
opposite central point. The ambient two-rank bound then leaves exactly the
two symmetric cases and the asymmetric rank-two/index-two case.

Reversal carries every H-invariant label by a single conjugator and exchanges
the literal ranks. A component commutator bound supplies both commutator
containments needed by the natural/dual orbit consumer. The final theorem
constructs this geometry for H=Mc and U=conjugateSpanBy(localModule T M) Mc.
It retains the non-FF and two-rank model premises; it does not assert their
source construction or the low-rank natural/dual image profiles.

Source: Aschbacher--Smith, 14.6.24(b), printed p.1039, and 14.6.24(4), p.1041;
F.9.13--17, pp.322--324.
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]

/-- Geometry at a selected original endpoint, with literal two-core
intersections and the action on the original quotient. -/
structure Geometry {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (ρ : Representation (ZMod 2) (Source.Hstar D.H) E) where
  pair : CriticalPair D.L (D.T : Subgroup G) D.H D.V
  endpoint : h.CriticalEndpoint
  representative_eq : endpoint.representative = (pair.gb : G)
  track_lower : 3 ≤ h.b
  denominator_eq : Source.DH D.UH (endpoint.conjugate D.UH) (endpoint.conjugate D.V₁) =
    D.UH ⊓ endpoint.conjugate D.QH
  opposite_denominator_eq : Source.Dgamma (endpoint.conjugate D.UH) D.UH D.V₁ =
    endpoint.conjugate D.UH ⊓ D.QH
  denominator_strict : D.UH ⊓ endpoint.conjugate D.QH < D.UH
  opposite_denominator_strict : endpoint.conjugate D.UH ⊓ D.QH < endpoint.conjugate D.UH
  denominator_pos : 0 < Nat.log 2 ((D.UH ⊓ endpoint.conjugate D.QH).relIndex D.UH)
  comparison : Nat.log 2 ((D.UH ⊓ endpoint.conjugate D.QH).relIndex D.UH) ≤
    rank (Source.starImage D.H (endpoint.conjugate D.UH))
  actor_rank_le_two : rank (Source.starImage D.H (endpoint.conjugate D.UH)) ≤ 2
  actor_quadratic : Reorientation.QuadraticMember ρ (Source.starImage D.H (endpoint.conjugate D.UH))
  actor_nonff : rank (Source.starImage D.H (endpoint.conjugate D.UH)) <
    fixedCodim ρ (Source.starImage D.H (endpoint.conjugate D.UH))
  opposite_index : (endpoint.conjugate D.UH ⊓ D.QH).relIndex (endpoint.conjugate D.UH) =
    Nat.card (Source.starImage D.H (endpoint.conjugate D.UH))
  point_commutator : ⁅D.UH ⊓ endpoint.conjugate D.QH, endpoint.conjugate D.UH⁆ =
    endpoint.conjugate D.V₁

/-- Non-FF action and ambient two-rank at most two select the actual
rank-one/rank-two critical geometry. Neither a selected pair nor a
commutator-image conclusion is an input. -/
theorem exists_geometry (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V) [IsElementaryAbelian 2 D.UH]
    (h62 : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (hnonff : ¬ IsFFModule ρ) (hrank : primeRank 2 (Source.Hstar D.H) ≤ 2) :
    Nonempty (Geometry h ρ) := by
  have hno (a : Source.Hstar D.H) (ha : orderOf a = 2) :
      2 ≤ fixedCodim ρ (zpowers a) := by
    have hA : IsElementaryTwo (zpowers a) := by
      refine ⟨?_,IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa only [ha] using pow_orderOf_eq_one a)⟩
      intro he
      have ha1 : a = 1 := by simpa only [he,mem_bot] using mem_zpowers a
      simp [ha1] at ha
    have hr : rank (zpowers a) = 1 := by simp only [rank,Nat.card_zpowers,ha]; decide
    have hn : ¬ fixedCodim ρ (zpowers a) ≤ rank (zpowers a) :=
      fun hc => hnonff ⟨zpowers a,hA,hc⟩
    omega
  obtain ⟨c,hb,hD,hDg,hpos,hcomp,hquad⟩ :=
    AlternatingSix.exists_critical_quadratic_selection D h hplus h62 s hno
  obtain ⟨i,hi⟩ := f9_criticalPair_endpoint D h c (by omega)
  have hU : i.conjugate D.UH = c.Ugamma D.Vplus := by
    change D.UH.map (MulAut.conj i.representative).toMonoidHom = _
    rw [hi]
    rfl
  have hZ : i.conjugate D.V₁ = c.Aone D.V₁ := by
    change D.V₁.map (MulAut.conj i.representative).toMonoidHom = _
    rw [hi]
    rfl
  have hQ : i.conjugate D.QH = c.Qgamma := by
    change D.QH.map (MulAut.conj i.representative).toMonoidHom = _
    rw [hi]
    rfl
  have htrack : 3 ≤ h.b := by
    rwa [c.length_eq,f9_criticalDistance_eq D h] at hb
  obtain ⟨hDeq,hDgeq⟩ := f9_endpoint_kernels D h c hb
  have hD' : D.UH ⊓ i.conjugate D.QH < D.UH := by rw [hQ,←hDeq]; exact hD
  have hDg' : i.conjugate D.UH ⊓ D.QH < i.conjugate D.UH := by rw [hU,←hDgeq]; exact hDg
  have hcomparison : Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) ≤
      rank (Source.starImage D.H (i.conjugate D.UH)) := by
    rw [hU,hQ,←hDeq]
    exact hcomp
  have hquad' : Reorientation.QuadraticMember ρ (Source.starImage D.H (i.conjugate D.UH)) :=
    hU.symm ▸ hquad
  have hnonff' : rank (Source.starImage D.H (i.conjugate D.UH)) <
      fixedCodim ρ (Source.starImage D.H (i.conjugate D.UH)) :=
    lt_of_not_ge (fun hc => hnonff ⟨_,hquad'.1,hc⟩)
  have hγH : i.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (i.large_le htrack)
  have hUA : D.UH ≤ normalizer (i.conjugate D.V₁ : Set G) :=
    ((conjugateSpanBy_mono h.plus_le le_rfl).trans (i.reverse_le htrack)).trans
      ((s.centralizes_conjugate_line i.representative).trans (Subgroup.centralizer_le_normalizer _))
  have hde : Source.DH D.UH (i.conjugate D.UH) (i.conjugate D.V₁) =
      D.UH ⊓ i.conjugate D.QH := by rw [hU,hZ,hQ]; exact hDeq
  refine ⟨{
    pair := c, endpoint := i, representative_eq := hi, track_lower := htrack
    denominator_eq := hde
    opposite_denominator_eq := by rw [hU]; exact hDgeq
    denominator_strict := hD'
    opposite_denominator_strict := hDg'
    denominator_pos := ?_
    comparison := hcomparison
    actor_rank_le_two := hquad'.1.rank_le_of_primeRank_le hrank
    actor_quadratic := hquad'
    actor_nonff := hnonff'
    opposite_index := ?_
    point_commutator := ?_
  }⟩
  · have hz : (D.UH ⊓ i.conjugate D.QH).relIndex D.UH ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hn : (D.UH ⊓ i.conjugate D.QH).relIndex D.UH ≠ 1 :=
      fun he => not_le_of_gt hD' (relIndex_eq_one.mp he)
    exact Nat.log_pos (by decide) (by omega)
  · change (i.conjugate D.UH ⊓ Source.QH D.H).relIndex _ = _
    rw [←s.Dgamma_eq_inf_core _ hγH (f9_section_faithful D h s)]
    exact s.Dgamma_relIndex _ hγH (f9_section_faithful D h s)
  · rw [←hde]
    apply f9_denominator_commutator_eq_point s hγH hUA
      ((card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card)
    rw [hde]
    exact hcomparison.trans_lt hnonff'

namespace Geometry
variable {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E} (q : Geometry h ρ)

omit [FiniteDimensional (ZMod 2) E] in
/-- The only selected numerical branches are the two symmetric ranks and
the rank-two actor with an index-two denominator. -/
theorem rank_cases :
    (rank (Source.starImage D.H (q.endpoint.conjugate D.UH)) = 1 ∧
      Nat.log 2 ((D.UH ⊓ q.endpoint.conjugate D.QH).relIndex D.UH) = 1) ∨
    (rank (Source.starImage D.H (q.endpoint.conjugate D.UH)) = 2 ∧
      Nat.log 2 ((D.UH ⊓ q.endpoint.conjugate D.QH).relIndex D.UH) = 2) ∨
    (rank (Source.starImage D.H (q.endpoint.conjugate D.UH)) = 2 ∧
      Nat.log 2 ((D.UH ⊓ q.endpoint.conjugate D.QH).relIndex D.UH) = 1) := by
  have := q.denominator_pos
  have := q.comparison
  have := q.actor_rank_le_two
  omega

omit [FiniteDimensional (ZMod 2) E] in
/-- Reversal transports every H-invariant label by the same element and
exchanges the literal actor and denominator ranks. -/
theorem reverse_labels_and_ranks
    (s : ConjugationSection D.H D.UH D.V₁ ρ) :
    ∃ j : h.CriticalEndpoint,
      (∀ A : Subgroup G, D.H ≤ normalizer (A : Set G) →
        j.conjugate (q.endpoint.conjugate A) = A) ∧
      rank (Source.starImage D.H (j.conjugate D.UH)) =
        Nat.log 2 ((D.UH ⊓ q.endpoint.conjugate D.QH).relIndex D.UH) ∧
      Nat.log 2 ((D.UH ⊓ j.conjugate D.QH).relIndex D.UH) =
        rank (Source.starImage D.H (q.endpoint.conjugate D.UH)) := by
  have hn : ¬ q.endpoint.conjugate D.UH ≤ D.QH := by
    intro hn
    exact not_le_of_gt q.opposite_denominator_strict (le_inf le_rfl hn)
  obtain ⟨j,hj⟩ := q.endpoint.reverse_labels q.track_lower hn
  have hU : j.conjugate (q.endpoint.conjugate D.UH) = D.UH :=
    hj D.UH (le_normalizer_conjugateSpanBy _ _)
  have hQ : j.conjugate (q.endpoint.conjugate D.QH) = D.QH :=
    hj D.QH (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D))
  have hγH : j.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (j.large_le q.track_lower)
  have hi : (j.conjugate D.UH ⊓ D.QH).relIndex (j.conjugate D.UH) =
      Nat.card (Source.starImage D.H (j.conjugate D.UH)) := by
    change (j.conjugate D.UH ⊓ Source.QH D.H).relIndex _ = _
    rw [←s.Dgamma_eq_inf_core _ hγH (f9_section_faithful D h s)]
    exact s.Dgamma_relIndex _ hγH (f9_section_faithful D h s)
  have hd : j.conjugate (D.UH ⊓ q.endpoint.conjugate D.QH) =
      j.conjugate D.UH ⊓ D.QH := by
    rw [ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.conjugate,
      map_inf _ _ _ (MulAut.conj j.representative).injective]
    exact congrArg (j.conjugate D.UH ⊓ ·) hQ
  have hdg : j.conjugate (q.endpoint.conjugate D.UH ⊓ D.QH) =
      D.UH ⊓ j.conjugate D.QH := by
    rw [ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.conjugate,
      map_inf _ _ _ (MulAut.conj j.representative).injective]
    exact congrArg (· ⊓ j.conjugate D.QH) hU
  refine ⟨j,hj,?_,?_⟩
  · rw [rank,←hi,←hd]
    congr 1
    exact relIndex_map_map_of_injective _ _ (MulAut.conj j.representative).injective
  · have he := relIndex_map_map_of_injective
      (f := (MulAut.conj j.representative).toMonoidHom)
      (q.endpoint.conjugate D.UH ⊓ D.QH) (q.endpoint.conjugate D.UH)
      (MulAut.conj j.representative).injective
    change (j.conjugate (q.endpoint.conjugate D.UH ⊓ D.QH)).relIndex
      (j.conjugate (q.endpoint.conjugate D.UH)) = _ at he
    rw [hdg,hU,q.opposite_index] at he
    exact congrArg (Nat.log 2) he

omit [FiniteDimensional (ZMod 2) E] in
/-- The whole H-commutator bound from the component decomposition gives
both required commutator containments. The selected geometry supplies the
opposite central point inside that same commutator. -/
theorem commutator_inputs (B : Subgroup G) (hB : ⁅D.UH,D.H⁆ ≤ B) :
    ⁅D.UH,q.endpoint.conjugate D.UH⁆ ≤ B ∧
    ⁅D.UH,q.endpoint.conjugate D.UH⁆ ≤ q.endpoint.conjugate B ∧
    q.endpoint.conjugate D.V₁ ≤ ⁅D.UH,q.endpoint.conjugate D.UH⁆ := by
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hγH := (map_mono huv).trans (q.endpoint.large_le q.track_lower)
  have hUH := huv.trans (q.endpoint.reverse_le q.track_lower)
  refine ⟨(commutator_mono le_rfl hγH).trans hB,?_,?_⟩
  · have hm := map_mono (f := (MulAut.conj q.endpoint.representative).toMonoidHom) hB
    rw [map_commutator] at hm
    rw [commutator_comm]
    exact (commutator_mono le_rfl hUH).trans hm
  · rw [←q.point_commutator]
    exact commutator_mono inf_le_left le_rfl
end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
/-- Application to the original terminal H=Mc and U=⟨V^Mc⟩. The two
remaining inputs are the non-FF result and the two-rank bound for the
literal quotient action, supplied by 14.6.20--23 and the single L3(2) model. -/
theorem source_selected_endpoint
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (s : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) ρ)
    (hnonff : ¬ IsFFModule ρ) (hrank : primeRank 2 (Source.Hstar Mc) ≤ 2) :
    Nonempty (Geometry
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) ρ) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  have h : D.Hypothesis :=
    ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  exact exists_geometry D h rfl
    (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hunique hmany hcard e hab)
    s hnonff hrank

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
