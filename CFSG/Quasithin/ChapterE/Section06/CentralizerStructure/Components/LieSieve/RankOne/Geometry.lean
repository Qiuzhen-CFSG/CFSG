module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# The actual rank-one Borel in E.6.8

The three concrete Bender models have a unique maximal proper overgroup of
each Sylow two-subgroup. The matrix proofs underlying F.1.3 establish this
without any local Chapter F hypotheses. Restricting the Sylow subgroup of
C_G(U) to its component and using L ≰ M therefore puts L ∩ M inside that
normalizer. The normalizer is also the full preimage of the Borel in L/Z(L),
by the central-quotient normalizer comparison.

This proves the unique-parabolic step, but not the opposite containment in M.
The latter needs the source local argument excluding A₃-blocks away from
PSL₂(4). The action of the Borel on V is a further obligation; no
`BorelAlternative` or action-dimension premise is used below.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterF.Source

variable {G : Type*} [Group G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- The Bender list with its field exponent retained. For PSU₃ this is
the exponent of the fixed-field order, not of the matrix-field order. -/
inductive Model (L : Subgroup G) (n : ℕ) : Prop
  | linear (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
  | unitary (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSU L 3 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m) (hn : n = 2 * m + 1)
      (iso : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))

/-- Preserve the actual equivalence and its parameter when dispatching the
three constructors of `IsBenderModel`. -/
theorem exists_model (hm : IsBenderModel L) : ∃ n, Model L n := by
  cases hm with
  | linear n hn iso => exact ⟨n, .linear hn iso⟩
  | unitary n hn iso => exact ⟨n, .unitary hn iso⟩
  | suzuki m hm iso => exact ⟨2 * m + 1, .suzuki m hm rfl iso⟩

theorem Model.one_lt {n : ℕ} (hm : Model L n) : 1 < n := by
  cases hm <;> omega

/-- The indexed model supplies exactly the corresponding E.6.8 model clause. -/
theorem Model.borelComponentModel {n : ℕ} (hm : Model L n) :
    BorelComponentModel L n := by
  cases hm with
  | linear hn iso => exact .linear_two (by omega) iso
  | unitary hn iso => exact .unitary_three (by omega) iso
  | suzuki m hm hn iso => exact .suzuki m hm hn iso

/-- Apply the proved concrete Sylow-normalizer theorems, retaining the
linear, fixed-field unitary, and actual Suzuki equivalences. -/
theorem Model.sylowFacts {n : ℕ} (hm : Model L n) (S : Sylow 2 L) :
    RankOneSylowFacts S := by
  apply IsRankOneModel.rankOneSylowFacts
  cases hm with
  | linear hn iso => exact .linear n (by omega) iso
  | unitary hn iso => exact .projective_unitary n (by omega) iso
  | suzuki m _ _ iso => exact .suzuki m iso

/-- Embed the normalizer of the prescribed Sylow subgroup in the ambient G. -/
def sylowBorel (S : Sylow 2 L) : Subgroup G :=
  (normalizer (S : Set L)).map L.subtype

theorem sylowBorel_le (S : Sylow 2 L) : sylowBorel S ≤ L :=
  map_subtype_le _

theorem sylowBorel_subgroupOf (S : Sylow 2 L) :
    (sylowBorel S).subgroupOf L = normalizer (S : Set L) :=
  comap_map_eq_self_of_injective L.subtype_injective _

/-- This normalizer is the Borel specified in the actual central quotient,
with no simplicity or centerlessness assumption. -/
theorem sylowBorel_preimage [Finite G] (S : Sylow 2 L) :
    BorelPreimage L (sylowBorel S) := by
  refine ⟨sylowBorel_le S, S.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [sylowBorel_subgroupOf, S.normalizer_comap_quotient_center]

/-- Identify the embedded normalizer with N_L(L ∩ Q), for the marked Sylow. -/
theorem sylowBorel_eq (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    sylowBorel S = L ⊓ normalizer ((L ⊓ Q : Subgroup G) : Set G) := by
  have hs : (L ⊓ Q).subgroupOf L = (S : Subgroup L) := by
    rw [← hS]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  change (normalizer ((S : Subgroup L) : Set L)).map L.subtype = _
  rw [← hs, ← subgroupOf_normalizer_eq (show L ⊓ Q ≤ L from inf_le_left),
    subgroupOf_map_subtype, inf_comm]

/-- The proper-overgroup theorem for the actual embedded Sylow subgroup.
In rank one this is stronger than uniqueness among proper parabolics. -/
theorem Model.proper_overgroup_le {n : ℕ} (hm : Model L n)
    (S : Sylow 2 L) {A : Subgroup G}
    (hSA : (S : Subgroup L).map L.subtype ≤ A) (hAL : A < L) :
    A ≤ sylowBorel S := by
  rw [← map_subgroupOf_eq_of_le hAL.le]
  apply map_mono
  apply (hm.sylowFacts S).unique_maximal
  · exact map_le_iff_le_comap.mp hSA
  · apply lt_top_iff_ne_top.mpr
    intro he
    apply hAL.ne
    rw [← map_subgroupOf_eq_of_le hAL.le, he]
    exact (MonoidHom.range_eq_map L.subtype).symm.trans L.range_subtype

/-- The canonical rank-one Borel is proper in L. -/
theorem Model.sylowBorel_lt {n : ℕ} (hm : Model L n) (S : Sylow 2 L) :
    sylowBorel S < L := by
  refine lt_of_le_of_ne (sylowBorel_le S) ?_
  intro he
  apply (hm.sylowFacts S).proper.ne
  apply Subgroup.map_injective L.subtype_injective
  simpa only [sylowBorel, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using he

/-- The canonical Borel is the unique maximal proper parabolic over S. -/
theorem Model.maximalParabolic {n : ℕ} (hm : Model L n) (S : Sylow 2 L) :
    MaximalParabolic L (sylowBorel S) := by
  refine ⟨sylowBorel_le S, ?_, S, (sylowBorel_subgroupOf S).ge⟩
  rw [sylowBorel_subgroupOf]
  refine ⟨(hm.sylowFacts S).proper.ne, ?_⟩
  intro A hA
  by_contra hne
  exact hA.not_ge ((hm.sylowFacts S).unique_maximal A
    ((S : Subgroup L).le_normalizer.trans hA.le) (lt_top_iff_ne_top.mpr hne))

/-- The actual component intersection lies in the unique rank-one Borel.
The opposite containment is the remaining placement step of E.6.8. -/
theorem intersection_le_sylowBorel [Finite G]
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hm : Model L n) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    L ⊓ M ≤ sylowBorel S := by
  apply hm.proper_overgroup_le S
  · rw [hS]
    exact inf_le_inf_left L (inf_le_left.trans h.sylow_le)
  · exact inf_lt_left.mpr (component_not_le h earlier hU hL)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
