module

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Preparation

/-!
# The actual point core in original 13.1.12

For a selected u, put S=C_T(u). The moved subgroup lies in O₂(N_G(L)),
which lies in O₂(XT), so u belongs to R=C_{O₂(XT)}(u) and R is nontrivial.
The module-orbit input makes R normal in XT, hence R ≤ O₂(XS).
Conversely O₂(XS) lies in S and is an X-signalizer. Its join with O₂(XT)
is a two-subgroup of T, so A.4.2 maximality gives the reverse containment.
Thus the core used in the local pushing-up argument is exactly O₂(XS).

This retains the point-centralizer intersection: it does not use the printed
intermediate equality R=O₂(XT), which is unnecessary for A.4.2(7).
Source: Aschbacher--Smith, 13.1.12(3), printed p.873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter12.Section02 SourceNonquasisimple
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ}

/-- The selected involution belongs to the literal point core. -/
theorem Context.selected_mem_core (h : Context T L p) {u : G} (s : Selected T L u) :
    u ∈ centralizerCore T L p u := by
  have hUM := (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal
    h.sylow_normalizes).2.2.1
  have hXTM : XiP p L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le ((XiP_le p L).trans L.le_normalizer) h.sylow_normalizes
  exact ⟨pCoreIn_le_pCoreIn_of_sylow T le_sup_right hXTM (hUM s.mem),
    mem_centralizer_singleton_iff.mpr rfl⟩


/-- In particular, the point core is nontrivial. -/
theorem Context.core_ne_bot (h : Context T L p) {u : G} (s : Selected T L u) :
    centralizerCore T L p u ≠ ⊥ := by
  intro hb
  exact s.ne_one (mem_bot.mp (hb ▸ h.selected_mem_core s))

variable [Fact p.Prime]

/-- The literal core identity needed for A.4.2(7) at C_G(u). -/
theorem Context.core_eq_local_join (h : Context T L p) (o : OrbitFacts T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    centralizerCore T L p u =
      (XiP p L ⊔ ((T : Subgroup G) ⊓ centralizer ({u} : Set G))).pCoreIn 2 := by
  let X := XiP p L
  let M := normalizer (L : Set G)
  let H := centralizer ({u} : Set G)
  let S := (T : Subgroup G) ⊓ H
  let J := X ⊔ S
  let Q := J.pCoreIn 2
  let B := (X ⊔ (T : Subgroup G)).pCoreIn 2
  have hXM : X ≤ M := (XiP_le p L).trans L.le_normalizer
  have hXH : X ≤ H := (XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1
    h.nonquasisimple p s.mem).trans inf_le_right
  have hJM : J ≤ M ⊓ H := sup_le (le_inf hXM hXH)
    (le_inf (inf_le_left.trans h.sylow_normalizes) inf_le_right)
  have hST : IsSylowIn 2 S J := s.local_sylow.restrict le_sup_right hJM
  obtain ⟨P,hP⟩ := hST
  have hQS : Q ≤ S := (pCoreIn_le_sylow J P).trans_eq hP
  have hQT : Q ≤ (T : Subgroup G) := hQS.trans inf_le_left
  have hBT : B ≤ (T : Subgroup G) := by
    have hb := pCoreIn_le_sylow (X ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hb
  have hmax := normal_sylow_core_isMaximal X M hXM
    (normalizer_le_normalizer_XiP p L) (XiP_isPPerfect p L) (T.subtype h.sylow_normalizes)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
    (show (T : Subgroup G) ≤ M from h.sylow_normalizes)] at hmax
  have hm := (isMaximalTwoSignalizer_iff X M B).mp hmax
  have hXQ : X ≤ normalizer (Q : Set G) := le_sup_left.trans
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hQB : Q ≤ B := le_sup_right.trans (hm.2 (B ⊔ Q)
    ((isTwoSignalizer_iff _ _ _).mpr
      ⟨(sup_le hBT hQT).trans h.sylow_normalizes,
        T.isPGroup'.to_le (sup_le hBT hQT),
        (le_inf hm.1.normalizes hXQ).trans (normalizer_inf_normalizer_le_normalizer_sup B Q)⟩)
    le_sup_left)
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le inf_le_left)
      ((le_inf (inf_le_left.trans hBT) inf_le_right).trans le_sup_right)
      ((sup_le_sup_left (show S ≤ (T : Subgroup G) from inf_le_left) X).trans
        (h.core_normalized o s hnt))
  · exact le_inf hQB (hQS.trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
