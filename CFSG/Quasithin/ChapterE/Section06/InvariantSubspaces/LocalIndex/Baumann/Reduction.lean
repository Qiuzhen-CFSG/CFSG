module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Assembly

/-!
# Reductions for the local single-block Baumann calculation

The elementary subgroup argument only needs C_H(U) = O₂(H) and Q ≤ S.
Here L and S are normalized by R, so LS is normal in H = LR. Its core is
therefore Q = LS ∩ O₂(H), and the characteristic elementary layer U lies
in Q. These facts give the three required Baumann fields from the two inputs.

The common-normal-subgroup exclusion forces J(R) outside O₂(H): otherwise
Thompson heredity identifies it with J(O₂(H)), which is normalized by H
as well as A. Thus, once C.1.11 is supplied, J(R) acts nontrivially on U.
This uses only the stated local configuration and avoids a further
application of C.1.26 in the already single-block setting.

For the A₅ case we also prove that the alpha decomposition of B.2.18(2)
implies Q ≤ S. Part (1) alone only puts the intrinsic O₂(L) in S; the
larger Q is handled using Q ≤ LS and its centralization of U.

The three input definitions are outstanding earlier results. This module
proves the reductions, not those inputs or the unconditional C.5.4 theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.3–4,
printed pp.154–155; C.1.11, p.124; B.2.3, pp.74–75; B.2.18, pp.80–81.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann

open Subgroup Stellmacher
universe u
variable {G : Type u} [Group G]

/-- The normal single-block specialization of C.1.11, with relative normality
and an actual chi-zero model. This is an earlier theorem to be proved, not a
consequence of the definitions. -/
@[expose] def SingleBlockCentralizerInput [Finite G] : Prop :=
  ∀ H R L : Subgroup G, HasCharacteristicTwo H → Chapter1.IsSylowIn 2 R H →
    H ≤ normalizer (L : Set G) → L ⊔ R = H → ChapterC.IsChiZeroBlock L →
    H ⊓ centralizer (U L : Set G) = pCoreIn 2 H

/-- The part of Baumann's Lemma needed for the natural rank-one cases.
C.1.11 is an explicit input so this calculation can be proved independently. -/
@[expose] def RankOneCoreInput [Finite G] (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L →
    H ⊓ centralizer (U L : Set G) = pCoreIn 2 H →
    ((∃ n, ChapterC.IsL2EvenBlock L n) ∨ ChapterC.IsAlternatingBlock L 3) →
    Q R L ≤ S R

/-- The weak alpha decomposition sufficient for the alternating-five case.
It follows from B.2.18(2) after the actual A₅ offender calculation; none of
that representation calculation is part of this definition. -/
@[expose] def AlternatingFiveAlphaInput [Finite G] (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L →
    H ⊓ centralizer (U L : Set G) = pCoreIn 2 H →
    ChapterC.IsAlternatingBlock L 5 →
    ChapterB.thompsonAlpha R ≤
      (ChapterB.thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔ U L

variable [Finite G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

omit [Finite G] in
private theorem normalizer_le_normalizer_J (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer (elementaryAbelianMaxJ B : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change B.map (MulAut.conj g).toMonoidHom = B at hg
  change (elementaryAbelianMaxJ B).map (MulAut.conj g).toMonoidHom = elementaryAbelianMaxJ B
  rw [← elementaryAbelianMaxJ_map_equiv, hg]

omit [Finite G] in
private theorem J_le (B : Subgroup G) : elementaryAbelianMaxJ B ≤ B :=
  sSup_le fun _ hE => hE.1

private theorem J_eq_of_intermediate (B C : Subgroup G)
    (hJ : elementaryAbelianMaxJ B ≤ C) (hCB : C ≤ B) :
    elementaryAbelianMaxJ B = elementaryAbelianMaxJ C := by
  obtain ⟨hc, hCJ⟩ := elementaryAbelianMaxOrder_le_and_j_le_of_eq C B hCB
  obtain ⟨hb, hBJ⟩ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le B C hJ
  exact le_antisymm (hBJ (le_antisymm hb hc)) (hCJ (le_antisymm hc hb))

omit [Finite G] in
/-- The block module is embedded by the literal subtype inclusion. -/
theorem module_le_L : U L ≤ L := map_subtype_le _

omit [Finite G] in
/-- The characteristic commutator layer of L is normalized by H. -/
theorem normalizes_module (h : Configuration K A H R L) :
    H ≤ normalizer (U L : Set G) :=
  h.normalizes_L.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))

omit [Finite G] in
/-- The short-group hypothesis supplies the actual elementary layer. -/
theorem module_elementary (h : Configuration K A H R L) : IsElementaryAbelian 2 (U L) :=
  h.block.chi.short.elementary.map L.subtype

omit [Finite G] in
/-- Irreducibility of the noncentral block quotient makes U nontrivial. -/
theorem module_ne_bot (h : Configuration K A H R L) : U L ≠ ⊥ := by
  intro he
  exact h.block.chi.short.blockU_ne_bot
    ((map_injective L.subtype_injective) (he.trans (map_bot L.subtype).symm))

omit [Finite G] in
/-- The local two-core lies in the supplied Sylow subgroup of H. -/
theorem HCore_le_R (h : Configuration K A H R L) : pCoreIn 2 H ≤ R := by
  obtain ⟨P, hP⟩ := h.sylow
  exact hP ▸ pCoreIn_le_sylow H P

/-- The H-normal elementary block layer lies in O₂(H). -/
theorem module_le_HCore (h : Configuration K A H R L) : U L ≤ pCoreIn 2 H := by
  let _ := module_elementary h
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (U L))
    (module_le_L.trans (h.join_eq ▸ le_sup_left)) (normalizes_module h)

/-- The block layer lies in the supplied Sylow subgroup, without a Baumann input. -/
theorem module_le_R (h : Configuration K A H R L) : U L ≤ R :=
  (module_le_HCore h).trans (HCore_le_R h)

/-- The nontrivial block layer excludes the trivial Sylow subgroup. -/
theorem sylow_ne_bot (h : Configuration K A H R L) : R ≠ ⊥ := by
  intro hz
  exact module_ne_bot h (le_bot_iff.mp (hz ▸ module_le_R h))

/-- The common-normal exclusion supplies the nonnormality in B.6.1. -/
theorem sylow_not_normalized_by_H (h : Configuration K A H R L) :
    ¬ H ≤ normalizer (R : Set G) := by
  intro hn
  apply h.no_common
  refine ⟨R, le_rfl, sylow_ne_bot h, Chapter3.normalIn_iff_le_normalizer.mpr ?_⟩
  rw [Chapter3.generated_eq_sup]
  exact ⟨h.le_A.trans le_sup_left, sup_le h.normalizes_R hn⟩

/-- Two-perfection makes the block commutator layer satisfy [U,L] = U. -/
theorem module_commutator_eq (h : Configuration K A H R L) : ⁅U L, L⁆ = U L := by
  have hi := commutator_isPPerfect_idempotent L (pCoreIn 2 L)
    h.block.chi.short.twoPerfect (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  simpa only [pCoreIn, U, ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map,
    range_subtype] using hi

/-- The local group H normalizes LS, using the characteristicity of Baum(R). -/
theorem normalizes_block_baumann_join (h : Configuration K A H R L) :
    H ≤ normalizer ((L ⊔ S R : Subgroup G) : Set G) := by
  rw [← h.join_eq]
  apply sup_le (le_sup_left.trans (L ⊔ S R).le_normalizer)
  exact (le_inf ((h.join_eq ▸ le_sup_right).trans h.normalizes_L)
    (h.le_A.trans h.normalizes_S)).trans
    (normalizer_inf_normalizer_le_normalizer_sup L (S R))

/-- Both L and Baum(R) are subgroups of the local group H. -/
theorem block_baumann_join_le_H (h : Configuration K A H R L) : L ⊔ S R ≤ H := by
  rw [← h.join_eq]
  exact sup_le_sup_left (show S R ≤ R from inf_le_left) L

/-- The characteristic core of the H-normal subgroup LS lies in O₂(H). -/
theorem localCore_le_HCore (h : Configuration K A H R L) : Q R L ≤ pCoreIn 2 H :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (L ⊔ S R))
    ((pCoreIn_le 2 _).trans (block_baumann_join_le_H h))
    ((normalizes_block_baumann_join h).trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ S R) (pCore 2 (L ⊔ S R : Subgroup G))))

/-- The elementary H-normal module lies in the local core Q. -/
theorem module_le_localCore (h : Configuration K A H R L) : U L ≤ Q R L := by
  let _ := module_elementary h
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (U L))
    (module_le_L.trans le_sup_left)
    ((block_baumann_join_le_H h).trans (normalizes_module h))

/-- The two-core of LS is its intersection with the two-core of H. -/
theorem localCore_eq_inter (h : Configuration K A H R L) :
    Q R L = (L ⊔ S R) ⊓ pCoreIn 2 H := by
  refine le_antisymm (le_inf (pCoreIn_le 2 _) (localCore_le_HCore h)) ?_
  apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).to_le inf_le_right) inf_le_left
  exact (le_inf (L ⊔ S R).le_normalizer
    ((block_baumann_join_le_H h).trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))).trans
    inf_normalizer_le_normalizer_inf

/-- Thompson heredity and the common-normal exclusion force J(R) outside O₂(H). -/
theorem thompson_not_le_HCore (h : Configuration K A H R L) :
    ¬ elementaryAbelianMaxJ R ≤ pCoreIn 2 H := by
  intro hj
  have he := J_eq_of_intermediate R (pCoreIn 2 H) hj (HCore_le_R h)
  have hJR : elementaryAbelianMaxJ R ≤ R := J_le R
  have hnH : H ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
    rw [he]
    exact (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
      (normalizer_le_normalizer_J _)
  have hnA : A ≤ normalizer (elementaryAbelianMaxJ R : Set G) :=
    h.normalizes_R.trans (normalizer_le_normalizer_J R)
  have hne : elementaryAbelianMaxJ R ≠ ⊥ := by
    intro hz
    obtain ⟨E, hE⟩ := elementaryAbelianMaxSubgroups_nonempty R
    have he0 : E = ⊥ := le_bot_iff.mp (hz ▸ (le_sSup hE))
    have hc := hE.2.2 (U L) (module_le_R h) (module_elementary h)
    simp only [he0, card_bot] at hc
    exact module_ne_bot h ((U L).eq_bot_of_card_le hc)
  apply h.no_common
  refine ⟨elementaryAbelianMaxJ R, hJR, hne, Chapter3.normalIn_iff_le_normalizer.mpr ?_⟩
  rw [Chapter3.generated_eq_sup]
  exact ⟨hJR.trans (h.le_A.trans le_sup_left), sup_le hnA hnH⟩

/-- C.1.11 converts Thompson escape into a nontrivial action on the block layer. -/
theorem thompson_moves_module (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (U L : Set G) := by
  intro hj
  apply thompson_not_le_HCore h
  rw [← hc]
  exact le_inf ((J_le R).trans (h.join_eq ▸ le_sup_right)) hj

/-- B.2.18(2)'s alpha decomposition, together with C.1.11, gives the
containment needed in C.5.4. The intrinsic core O₂(L) alone is insufficient:
we use that the whole Q lies in LS and centralizes U. -/
theorem localCore_le_baumann_of_alpha (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    (ha : ChapterB.thompsonAlpha R ≤
      (ChapterB.thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔ U L) :
    Q R L ≤ S R := by
  have hLC : L ≤ centralizer
      ((ChapterB.thompsonAlpha R ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  have hSC : S R ≤ centralizer
      ((ChapterB.thompsonAlpha R ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    (show S R ≤ centralizer (ChapterB.thompsonAlpha R : Set G) from inf_le_right).trans
      (centralizer_le inf_le_left)
  have hQC := (pCoreIn_le 2 (L ⊔ S R)).trans (sup_le hLC hSC)
  have hQU : Q R L ≤ centralizer (U L : Set G) :=
    (localCore_le_HCore h).trans (hc ▸ inf_le_right)
  have hQalpha : Q R L ≤ centralizer (ChapterB.thompsonAlpha R : Set G) :=
    le_centralizer_iff.mpr (ha.trans (sup_le
      (le_centralizer_iff.mp hQC) (le_centralizer_iff.mp hQU)))
  exact le_inf ((localCore_le_HCore h).trans (HCore_le_R h)) hQalpha

/-- The centralizer theorem and Q ≤ S imply all three required Baumann fields. -/
theorem structure_of_core_bound (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    (hq : Q R L ≤ S R) : BaumannStructure H R L := by
  refine ⟨(module_le_localCore h).trans hq, ?_, ?_⟩
  · rw [← hc]
    exact inf_le_inf_right _ (h.join_eq ▸ le_sup_right)
  · have hSC : S R ⊓ centralizer (U L : Set G) ≤ Q R L := by
      rw [localCore_eq_inter h, ← hc]
      exact le_inf (inf_le_left.trans le_sup_right)
        (le_inf (inf_le_left.trans ((show S R ≤ R from inf_le_left).trans
          (h.join_eq ▸ le_sup_right))) inf_le_right)
    exact le_antisymm (le_inf hq ((localCore_le_HCore h).trans (hc ▸ inf_le_right))) hSC

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann

end
