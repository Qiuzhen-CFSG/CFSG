module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MarkedSimpleSocle
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PerfectResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.Irreducibility

/-!
# A simple two-residual from the original perfect source factors

Use the original L₀ inside the literal generated carrier, followed by the
same quotient q used for both marked parabolics. Endpoint-kernel disjointness
makes this local map injective. Its range lies in the previously identified
perfect residual. The image of the original S equals the specified U and
normalizes this range; the original intrinsic Sylow of L₀ maps into U.

The proved rank-one quotient theorems supply the proper solvable Sylow
normalizer and uniqueness of proper Sylow overgroups. Thus normal generation
and solvability of proper normal local subgroups are proved, not extra source
premises. The carrier-general marked-quotient reduction now proves that the
literal O² of the quotient is simple. The original generated carrier need
not be finite. This does not assert that the geometric universal quotient
descends to this carrier: SourceQuotient remains the explicit input here.

This removes the simple-power multiplicity in the both-perfect branch of
the Fong–Seitz invocation in DGS, Groups and Graphs, pp.80–81 and224, using
Aschbacher–Smith F.1.1–3, pp.259–260. The full minimal-configuration reduction,
seven regular marked Lie comparisons, and nonperfect/binary branches remain
unproved. The earlier quotient and splitness producers and final source
assembly retain every extra premise discharge. No map or marking is changed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both original perfect factors force a simple residual in their marked quotient. -/
theorem quotient_twoResidual_isSimple (h : HypothesisF11 L S)
    (hp : ∀ i, Group.IsPerfect (L i)) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) : IsSimpleGroup (pResidual 2 ((generated L S) ⧸ Q.D)) := by
  let Y := (generated L S) ⧸ Q.D
  let K := pResidual 2 Y
  let := h.finite_local 0
  let := hp 0
  let : Nontrivial (L 0) := (L 0).nontrivial_iff_ne_bot.mpr
    (ne_bot_of_gt (h.rankOneBorelFacts 0).proper)
  have hc := quotient_parabolic_core_selfCentralizing h Q
  have hgen := quotient_unipotentClosure_eq_top h.S_isP hp Q split
  have hperf := (quotient_perfect_residual h hp Q).2
  let j : L 0 →* generated L S := inclusion (local_le_generated 0)
  let f := Q.q.comp j
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro a ha
    have hD : j a ∈ Q.D := (QuotientGroup.eq_one_iff _).mp ha
    have hP : j a ∈ (parabolic L S 0).subgroupOf (generated L S) :=
      (show L 0 ≤ parabolic L S 0 from le_sup_left.trans le_sup_left) a.property
    have he : j a = 1 := (disjoint_iff.mp (Q.disjoint 0)).le ⟨hD, hP⟩
    apply (L 0).subtype_injective
    exact congrArg (fun x : generated L S => (x : G)) he
  have hr : f.range = ((L 0).subgroupOf (generated L S)).map Q.q := by
    rw [MonoidHom.range_comp, inclusion_range]
  have hfK : f.range ≤ K := by
    change f.range ≤ pResidual 2 ((generated L S) ⧸ Q.D)
    rw [hr, (quotient_perfect_residual h hp Q).1]
    exact le_sup_left
  have hn : split.U ≤ normalizer (f.range : Set Y) := by
    rw [hr, ← quotient_sourceS_image_eq_unipotent h Q split]
    have hn0 : S.subgroupOf (generated L S) ≤
        normalizer ((L 0).subgroupOf (generated L S) : Set (generated L S)) :=
      (comap_mono (h.S_normalizes 0)).trans
        ((L 0).le_normalizer_comap (generated L S).subtype)
    exact (map_mono hn0).trans (((L 0).subgroupOf (generated L S)).le_normalizer_map Q.q)
  obtain ⟨T, hT⟩ := h.sylow 0
  have hTU : (T : Subgroup (L 0)).map f ≤ split.U := by
    rw [← quotient_sourceS_image_eq_unipotent h Q split]
    change ((T : Subgroup (L 0)).map (Q.q.comp j)) ≤ _
    rw [← map_map]
    apply map_mono
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact (hT.le (mem_map_of_mem (L 0).subtype ht)).1
  have facts := rankOneSylowFacts_of_rankOneQuotient (h.quotient 0) T
  exact Q.twoResidual_isSimple_of_local_factor split hc hgen hperf f hf hfK hn T hTU
    facts.proper facts.unique_maximal facts.solvable

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
