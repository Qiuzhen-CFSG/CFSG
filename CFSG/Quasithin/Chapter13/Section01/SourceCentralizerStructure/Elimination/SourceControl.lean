module

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.LocalCore
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.LocalSetup

/-!
# Local pushing-up control from the original radical's starred membership

The starred normalizer theorem identifies N_G(L) as the unique maximal
two-local over Ξ_p(L)T, using the proved equality of the radical and
component normalizers. Preparation then controls the characteristic
normalizers of the point core. The actual core identity, selected local
Sylow subgroup, and A.4.2(7) construct C.2.3 inside C_G(u), with the normal
closure taken under N_G(L)∩C_G(u).

This completes the implication from starred membership to the published
Control contract. Starred membership under Context is a separate source
obligation: this module does not assert Context → OrbitFacts → Control
until that exclusion has been proved. No universal A.3.12/C.2.7 callback
or maximal-overgroup uniqueness premise is used here.

Source: Aschbacher--Smith, 13.1.4(4--6), printed pp.867--868,
and 13.1.12(3), p.873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter12.Section02 SourceNonquasisimple
open Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The original starred normalizer theorem identifies every maximal two-local
above Ξ_p(L)T with the literal component normalizer. -/
theorem Context.unique_overgroup_of_radical_star (h : Context T L p)
    (hx : XiP p L ∈ XiStar G (T : Subgroup G))
    (M : Subgroup G) (hm : IsMaximalTwoLocal M)
    (hXM : XiP p L ⊔ (T : Subgroup G) ≤ M) : M = normalizer (L : Set G) := by
  have hu := (Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple
    h.hypothesis.simpleQTKE T hx).2
  have hh : M ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ XiP p L ⊔ (T : Subgroup G) ≤ N} :=
    ⟨hm,hXM⟩
  rw [hu] at hh
  exact (Set.mem_singleton_iff.mp hh).trans
    (RadicalConjugateRigidity.maximal_radical_structure h.hypothesis.simpleQTKE T
      h.maximal.1 h.nonquasisimple h.odd h.divides).2.1


/-- Supply every field of Control from the precise earlier starred-radical
exclusion. Final source assembly must discharge this remaining premise. -/
theorem Context.control_of_radical_star (h : Context T L p) (o : OrbitFacts T L p)
    (hx : XiP p L ∈ XiStar G (T : Subgroup G)) : Control T L p := by
  have hu := h.unique_overgroup_of_radical_star hx
  refine ⟨hu,?_⟩
  intro u s hnt
  apply pushingUp_setup_of_normal_sylow_core
    (h.hypothesis.simpleQTKE.involution_centralizer_sqtk (h.involution s.mem s.ne_one))
    inf_le_right
    (XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1 h.nonquasisimple p s.mem)
    (XiP_invariant p inf_le_left) (XiP_isPPerfect p L) s.local_sylow
    (h.core_eq_local_join o s hnt) (h.core_ne_bot s)
  intro g hg
  exact ⟨characteristicNormalizerClosure_subgroupOf_le
    (show centralizerCore T L p u ≤ centralizer ({u} : Set G) from inf_le_right)
    (h.core_characteristic_control o s hnt hu) hg,g.property⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
