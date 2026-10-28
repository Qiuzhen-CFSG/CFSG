module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCharacteristic

/-!
# The literal prime-actor pair and its nonzero-core extension

For original 5.2.2, set S = O₂(N_G(L) ∩ H), G₀ = ⟨D,L₂S⟩ and
T₀ = N_T(L₂). The source construction of L₂ and the small prime local
quotient remain explicit in `LocalData`. These are structural obligations,
not an assumed F.1.1 amalgam or classification conclusion. In particular
there is no assumption that the Cartan or D normalizes L₂.

With these inputs the zero-core branch satisfies genuine F.1.1: the two
Borel formulas give cross-normalization, and containment of the actual
source S gives both generalized-Fitting equalities. Its right parabolic
is nonsolvable. In the nonzero-core branch, normalization extends the
core to G₀T₀B; comparison with the original zero-core join ⟨D,H⟩ shows
H is outside that extension, T₀<T, and L₂<O²(H).

Source: Aschbacher--Smith, 5.1.10--11, 5.2.1--2, printed pp.634--635,
646--648 (`refs/quasithin.pdf`). The source construction, exceptional
model exclusions and changed-Sylow component argument remain to be proved.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The subgroup G₀=⟨D,L₂S⟩, with S in its original ambient group. -/
abbrev generated (L H D L₂ : Subgroup G) : Subgroup G :=
  D ⊔ (L₂ ⊔ Global.sourceS L H)

/-- The literal N_T(L₂), not asserted to be Sylow in G. -/
abbrev normalizingSylow (T : Sylow 2 G) (L₂ : Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ normalizer (L₂ : Set G)

/-- The source extension G₀T₀B, represented by its actual join. -/
abbrev extension (T : Sylow 2 G) (L H B D L₂ : Subgroup G) : Subgroup G :=
  generated L H D L₂ ⊔ normalizingSylow T L₂ ⊔ B

/-- Output contract for the source choice on pp.646--647. Its conditional
small-local clauses must be proved using the zero-core hypothesis. -/
structure LocalData (T : Sylow 2 G) (L H B D L₂ : Subgroup G) : Prop where
  right_le_residual : L₂ ≤ residual H
  right_outside : ¬ L₂ ≤ normalizer (L : Set G)
  right_generate : L₂ ⊔ (T : Subgroup G) = H
  right_nonsolvable : ¬ Group.IsSolvable L₂
  right_component :
    (L₂.subgroupOf (L₂ ⊔ normalizingSylow T L₂)).IsCComponent
  index_le_two : (normalizingSylow T L₂).relIndex (T : Subgroup G) ≤ 2
  S_intersection_residual : Global.sourceS L H ⊓ residual H =
    (T : Subgroup G) ⊓ residual H
  S_intersection_left : Global.sourceS L H ⊓ L = (T : Subgroup G) ⊓ L
  S_normalizes_right : Global.sourceS L H ≤ normalizer (L₂ : Set G)
  B_normalizes_right : B ≤ normalizer (L₂ : Set G)
  TB_normalizes_left : (T : Subgroup G) ⊔ B ≤
    normalizer ((D ⊔ Global.sourceS L H : Subgroup G) : Set G)
  right_sylow : ∃ P : Sylow 2 L₂,
    (P : Subgroup L₂).map L₂.subtype = Global.sourceS L H ⊓ L₂
  right_quotient : ChapterF.Source.IsRankOneModel (L₂ ⧸ pCore 2 L₂)
  right_borel : ChapterF.Source.borel L₂ (Global.sourceS L H) =
    (Global.sourceS L H ⊓ L₂) ⊔ (B ⊓ L₂)
  left_sylow : ∃ P : Sylow 2 (D ⊔ Global.sourceS L H : Subgroup G),
    (P : Subgroup (D ⊔ Global.sourceS L H : Subgroup G)).map
      (D ⊔ Global.sourceS L H : Subgroup G).subtype = Global.sourceS L H
  left_quotient : (generated L H D L₂).pCoreIn 2 = ⊥ →
    ChapterF.Source.IsRankOneModel
      ((D ⊔ Global.sourceS L H : Subgroup G) ⧸
        pCore 2 (D ⊔ Global.sourceS L H : Subgroup G))
  left_borel : (generated L H D L₂).pCoreIn 2 = ⊥ →
    ChapterF.Source.borel (D ⊔ Global.sourceS L H) (Global.sourceS L H) =
      Global.sourceS L H

omit [Finite G] in
/-- F.1.1 uses the very same generated subgroup G₀. -/
theorem generated_eq (L H D L₂ : Subgroup G) :
    ChapterF.Source.generated ![D ⊔ Global.sourceS L H, L₂] (Global.sourceS L H) =
      generated L H D L₂ := by
  change (D ⊔ Global.sourceS L H) ⊔ L₂ ⊔ Global.sourceS L H = _
  simp only [generated, sup_comm, sup_left_comm, sup_idem]

/-- Verify all genuine F.1.1 clauses for the pair (DS,L₂) under trivial core. -/
theorem LocalData.hypothesisF11 {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 = ⊥) :
    ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H, L₂] (Global.sourceS L H) := by
  let S := Global.sourceS L H
  have hSM : S ≤ normalizer (L : Set G) :=
    (Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans h.sylow_normalizes
  have hSK : S ≤ normalizer (residual H : Set G) :=
    (Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans
      (hH.1.1.2.trans (le_normalizer_residual H))
  have hDM : D ≤ normalizer (L : Set G) :=
    (hd.le_cartan.trans c.left_le).trans (inf_le_left.trans L.le_normalizer)
  have hb0 := d.left_borel hz
  refine ⟨inferInstance, pCore_isPGroup.map _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (show S ≤ D ⊔ S from le_sup_right).trans (D ⊔ S).le_normalizer
    · exact d.S_normalizes_right
  · intro i
    fin_cases i
    · obtain ⟨P, hP⟩ := d.left_sylow
      refine ⟨P, ?_⟩
      change (P : Subgroup (D ⊔ S : Subgroup G)).map (D ⊔ S : Subgroup G).subtype = S ⊓ (D ⊔ S)
      simpa only [inf_eq_left.mpr (show S ≤ D ⊔ S from le_sup_right)] using hP
    · exact d.right_sylow
  · intro i
    fin_cases i
    · exact d.left_quotient hz
    · exact d.right_quotient
  · intro i
    fin_cases i
    · change ChapterF.Source.borel L₂ S ≤ normalizer ((D ⊔ S : Subgroup G) : Set G)
      rw [d.right_borel]
      exact sup_le
        (inf_le_left.trans ((show S ≤ D ⊔ S from le_sup_right).trans (D ⊔ S).le_normalizer))
        (inf_le_left.trans (le_sup_right.trans d.TB_normalizes_left))
    · change ChapterF.Source.borel (D ⊔ S) S ≤ normalizer (L₂ : Set G)
      rw [hb0]
      exact d.S_normalizes_right
  · rw [generated_eq]
    exact (Subgroup.map_eq_bot_iff_of_injective
      (f := (generated L H D L₂).subtype) _ (generated L H D L₂).subtype_injective).mp hz
  · intro i
    fin_cases i
    · apply Global.characteristic_two_of_sourceS_left h hH.1.1.2
      · change (D ⊔ S) ⊔ S ⊔ ChapterF.Source.borel L₂ S ≤ _
        rw [d.right_borel]
        exact sup_le (sup_le (sup_le hDM hSM) hSM)
          (sup_le (inf_le_left.trans hSM) (inf_le_left.trans (c.right_le.trans inf_le_left)))
      · exact le_sup_right.trans le_sup_left
    · apply Global.characteristic_two_of_sourceS_right h hH
      · change L₂ ⊔ S ⊔ ChapterF.Source.borel (D ⊔ S) S ≤ _
        rw [hb0]
        exact sup_le (sup_le (d.right_le_residual.trans (residual H).le_normalizer) hSK) hSK
      · exact le_sup_right.trans le_sup_left

omit [Finite G] in
/-- T₀B normalizes both generators of G₀, hence the extension normalizes G₀. -/
theorem LocalData.extension_normalizes_generated
    {T : Sylow 2 G} {L H B D L₂ : Subgroup G}
    (d : LocalData T L H B D L₂) :
    extension T L H B D L₂ ≤ normalizer (generated L H D L₂ : Set G) := by
  have he : generated L H D L₂ = (D ⊔ Global.sourceS L H) ⊔ L₂ := by
    simp only [generated, sup_comm, sup_left_comm]
  have ht : normalizingSylow T L₂ ⊔ B ≤ normalizer (generated L H D L₂ : Set G) := by
    rw [he]
    apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact le_inf
      ((sup_le_sup_right (show normalizingSylow T L₂ ≤ (T : Subgroup G) from inf_le_left) B).trans
        d.TB_normalizes_left)
      (sup_le inf_le_right d.B_normalizes_right)
  exact sup_le (sup_le (generated L H D L₂).le_normalizer
    (le_sup_left.trans ht)) (le_sup_right.trans ht)

omit [Finite G] in
/-- Relative normality carries the nontrivial two-core into G₀T₀B. -/
theorem LocalData.extension_core_ne_bot
    {T : Sylow 2 G} {L H B D L₂ : Subgroup G}
    (d : LocalData T L H B D L₂) (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    (extension T L H B D L₂).pCoreIn 2 ≠ ⊥ := by
  have hc := pCoreIn_mono_of_normalizes
    (show generated L H D L₂ ≤ extension T L H B D L₂ from le_sup_left.trans le_sup_left)
    d.extension_normalizes_generated (p := 2)
  exact fun he => hz (bot_unique (he ▸ hc))

omit [Finite G] in
/-- Containment of H would identify G₀T₀B with the forbidden zero-core join. -/
theorem LocalData.hstar_not_le_extension
    {T : Sylow 2 G} {L H A B D L₂ : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D L₂) (hTH : (T : Subgroup G) ≤ H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    ¬ H ≤ extension T L H B D L₂ := by
  have hSH : Global.sourceS L H ≤ H := (map_subtype_le _).trans inf_le_right
  have he : extension T L H B D L₂ ≤ D ⊔ H := by
    exact sup_le
      (sup_le (sup_le le_sup_left
        (sup_le (d.right_le_residual.trans ((map_subtype_le _).trans le_sup_right))
          (hSH.trans le_sup_right))) (inf_le_left.trans (hTH.trans le_sup_right)))
      (c.right_le.trans (inf_le_right.trans le_sup_right))
  intro hHE
  have heq : extension T L H B D L₂ = D ⊔ H := le_antisymm he
    (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) hHE)
  exact d.extension_core_ne_bot hz (heq.symm ▸ hd.zero_core)

omit [Finite G] in
/-- The nonzero-core branch forces T₀ to be a proper subgroup of T. -/
theorem LocalData.normalizingSylow_lt
    {T : Sylow 2 G} {L H A B D L₂ : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D L₂) (hTH : (T : Subgroup G) ≤ H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    normalizingSylow T L₂ < (T : Subgroup G) := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro he
  apply d.hstar_not_le_extension hTH c hd hz
  rw [← d.right_generate, ← he]
  exact sup_le (le_sup_left.trans (le_sup_right.trans (le_sup_left.trans le_sup_left)))
    (le_sup_right.trans le_sup_left)

omit [Finite G] in
/-- The selected rank-one factor is then properly inside the original residual. -/
theorem LocalData.right_lt_residual
    {T : Sylow 2 G} {L H A B D L₂ : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D L₂) (hTH : (T : Subgroup G) ≤ H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) : L₂ < residual H := by
  refine lt_of_le_of_ne d.right_le_residual ?_
  intro he
  have hnorm : (T : Subgroup G) ≤ normalizer (L₂ : Set G) := by
    rw [he]
    exact hTH.trans (le_normalizer_residual H)
  exact (d.normalizingSylow_lt hTH c hd hz).ne (inf_eq_left.mpr hnorm)

omit [Finite G] in
/-- The second F.1.1 parabolic is literally L₂S. -/
theorem LocalData.parabolic_one
    {T : Sylow 2 G} {L H B D L₂ : Subgroup G}
    (d : LocalData T L H B D L₂) (hz : (generated L H D L₂).pCoreIn 2 = ⊥) :
    ChapterF.Source.parabolic ![D ⊔ Global.sourceS L H, L₂] (Global.sourceS L H) 1 =
      L₂ ⊔ Global.sourceS L H := by
  change L₂ ⊔ Global.sourceS L H ⊔
    ChapterF.Source.borel (D ⊔ Global.sourceS L H) (Global.sourceS L H) = _
  rw [d.left_borel hz, sup_assoc, sup_idem]

omit [Finite G] in
/-- The source nonsolvable rank-one factor excludes a solvable right parabolic. -/
theorem LocalData.right_parabolic_not_solvable
    {T : Sylow 2 G} {L H B D L₂ : Subgroup G}
    (d : LocalData T L H B D L₂) (hz : (generated L H D L₂).pCoreIn 2 = ⊥) :
    ¬ Group.IsSolvable (ChapterF.Source.parabolic
      ![D ⊔ Global.sourceS L H, L₂] (Global.sourceS L H) 1) := by
  rw [d.parabolic_one hz]
  intro hs
  let := hs
  exact d.right_nonsolvable (Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (show L₂ ≤ L₂ ⊔ Global.sourceS L H from le_sup_left)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
