module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Endpoints
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup

/-!
# An opposite pair from the actual odd critical track

A normalized odd critical endpoint gives both opposite-stabilizer containments.
The centralizer of its whole neighbor span lies in its first-ball kernel:
normality reduces this to the centralizer of the original seed in the second
vertex. Criticality therefore supplies a noncommuting conjugate seed. Changing
the endpoint representative inside the second vertex preserves both spans.

Only the two vertex stabilizers need be finite, as in the F.7 source setup.
No finiteness assumption on the coset graph is used.

Source: Aschbacher--Smith, Section 15.2, printed pp.1119--1120;
F.7.9--11, printed pp.313--314.
-/

public section

open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base incident_base)
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02.ChosenOppositeTrack
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem centralizer_span_le_kernel (D : SourceSetup F)
    (hc : F true ⊓ centralizer (D.seed : Set G) ≤ F false) :
    F true ⊓ centralizer (conjugateSpan (F true) D.seed : Set G) ≤
      ballKernel F (base F true) 1 := by
  let K := F true ⊓ centralizer (conjugateSpan (F true) D.seed : Set G)
  have hVK : D.seed ≤ conjugateSpan (F true) D.seed := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hn : F true ≤ normalizer (K : Set G) :=
    (le_inf (F true).le_normalizer
      ((conjugateSpan_normalized _ _).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  let : (K.subgroupOf (F true)).Normal := normal_subgroupOf_of_le_normalizer hn
  have hK : K ≤ F true ⊓ F false :=
    le_inf inf_le_left ((inf_le_inf_left _ (centralizer_le hVK)).trans hc)
  have hlocal : K.subgroupOf (F true) ≤
      ((F true ⊓ F false).subgroupOf (F true)).normalCore :=
    normal_le_normalCore.mpr (fun _ hx => hK hx)
  have hm := map_mono (f := (F true).subtype) hlocal
  rw [map_subgroupOf_eq_of_le (show K ≤ F true from inf_le_left)] at hm
  have he := ballKernel_one_eq_map_normalCore F
    (show (graph F).Adj (base F true) (base F false) from
      ⟨by change true ≠ false; decide, incident_base F true false⟩)
  rw [show stabilizer F (base F true) = F true from stabilizer_base F true,
    show stabilizer F (base F false) = F false from stabilizer_base F false] at he
  exact hm.trans_eq he.symm

/-- The F.7 source inputs construct an actual ambient conjugator with the
opposite-span containments and a nontrivial seed commutator. -/
theorem opposite_spans_of_not_ff (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hcore : D.seed ≤ (F true).pCoreIn 2)
    (hnot : ¬ SourceAction.IsFF D)
    (hc : F true ⊓ centralizer (D.seed : Set G) ≤ F false) :
    ∃ g : G,
      conjugateSpan (F true) D.seed ≤ (F true).map (MulAut.conj g).toMonoidHom ∧
      (conjugateSpan (F true) D.seed).map (MulAut.conj g).toMonoidHom ≤ F true ∧
      ⁅D.seed, D.seed.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  have hodd := Completion.odd_track_of_not_ff F D hne hnot
  have hsmall := Completion.one_lt_track_of_true_core F D hne hcore
  have hb : 3 ≤ D.track hne := by obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨i⟩ := NormalizedEndpoint.nonempty (D := D) (hne := hne) hodd
  let U := conjugateSpan (F true) D.seed
  have hbase : vertexModule F D.seed (base F true) = U :=
    second_base_module_eq_conjugate_join F D.seed D.seed_normalized
  have hi : vertexModule F D.seed i.vertex = U.map (MulAut.conj (i : G)).toMonoidHom := by
    rw [NormalizedEndpoint.vertex, vertexModule_translate, hbase]
    exact D.seed_normalized
  have hmove : ⁅D.seed, U.map (MulAut.conj (i : G)).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    apply i.property.2.2
    have hcent := commutator_eq_bot_iff_le_centralizer.mp he
    have hsub := le_inf i.seed_le_stabilizer hcent
    have hinv := map_mono (f := (MulAut.conj (i : G)⁻¹).toMonoidHom) hsub
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (i : G)⁻¹).injective,
      ← stabilizer_translate, NormalizedEndpoint.vertex, inv_smul_smul,
      show stabilizer F (base F true) = F true from stabilizer_base F true] at hinv
    have hcent' : (centralizer (U.map (MulAut.conj (i : G)).toMonoidHom : Set G)).map
        (MulAut.conj (i : G)⁻¹).toMonoidHom ≤ centralizer (U : Set G) := by
      have hh := map_centralizer_le_centralizer_image
        (U.map (MulAut.conj (i : G)).toMonoidHom : Set G)
        (MulAut.conj (i : G)⁻¹).toMonoidHom
      rw [← coe_map, CFSG.Quasithin.ChapterE.offender_map_conj_inverse] at hh
      exact hh
    have hk := hinv.trans ((inf_le_inf_left _ hcent').trans
      (centralizer_span_le_kernel D hc))
    have hk' := map_mono (f := (MulAut.conj (i : G)).toMonoidHom) hk
    have hid := CFSG.Quasithin.ChapterE.offender_map_conj_inverse D.seed (i : G)⁻¹
    rw [inv_inv] at hid
    rw [hid, ← ballKernel_translate] at hk'
    exact hk'
  have hex : ∃ t : F true,
      ⁅D.seed, (D.seed.map (MulAut.conj (t : G)).toMonoidHom).map
        (MulAut.conj (i : G)).toMonoidHom⁆ ≠ ⊥ := by
    by_contra hn
    apply hmove
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    change (⨆ t : F true, D.seed.map (MulAut.conj (t : G)).toMonoidHom).map _ ≤ _
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro t
    have he : ⁅D.seed, (D.seed.map (MulAut.conj (t : G)).toMonoidHom).map
        (MulAut.conj (i : G)).toMonoidHom⁆ = ⊥ :=
      Classical.byContradiction (fun h => hn ⟨t, h⟩)
    rw [commutator_comm] at he
    exact commutator_eq_bot_iff_le_centralizer.mp he
  obtain ⟨t, ht⟩ := hex
  have hH : (F true).map (MulAut.conj ((i : G) * (t : G))).toMonoidHom =
      (F true).map (MulAut.conj (i : G)).toMonoidHom := by
    rw [← CFSG.Quasithin.ChapterE.offender_map_conj_map]
    have hn : (F true).map (MulAut.conj (t : G)).toMonoidHom = F true :=
      mem_normalizer_iff_map_conj_eq.mp ((F true).le_normalizer t.property)
    rw [hn]
  have hU : U.map (MulAut.conj ((i : G) * (t : G))).toMonoidHom =
      U.map (MulAut.conj (i : G)).toMonoidHom := by
    rw [← CFSG.Quasithin.ChapterE.offender_map_conj_map]
    have hn : U.map (MulAut.conj (t : G)).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp
        (conjugateSpan_normalized (F true) D.seed t.property)
    rw [hn]
  refine ⟨(i : G) * (t : G), ?_, ?_, ?_⟩
  · rw [hH]
    have hh := i.reverse_module_le hb
    rw [hbase] at hh
    simpa only [NormalizedEndpoint.vertex, stabilizer_translate, stabilizer, base,
      stabilizer_base] using hh
  · rw [hU, ← hi]
    exact i.endpoint_module_le hb
  · rwa [← CFSG.Quasithin.ChapterE.offender_map_conj_map]

end CFSG.Quasithin.Chapter15.Section02.ChosenOppositeTrack
