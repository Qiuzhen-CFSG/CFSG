module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Seeds
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Quotients
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceNormalizer
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Literal Y_z selection for the ordinary A₇ replacement

A normalized two-perfect lift B with quotient B/O₂(B) isomorphic to A₆
belongs to the genuine selection family when it moves z and a Thompson
actor has a commutator outside O₂(B). Simplicity of A₆ and two-perfection
force [B,J(Tᵥ)] = B. Relative normality makes B a C-component of B Tᵥ;
the original local member supplies the Sylow and nontrivial two-core
conditions, which restrict to this smaller join.

The literal star projection has proper kernel because B moves z. The same
simple-quotient argument puts that kernel in O₂(B), giving an actual
isomorphism B*/O₂(B*) ≃ A₆. Normalization, residuals and commutators then
pass through the actual star map, establishing every X_z clause.

The constructed residual lift is an explicit consumer. The normalizer
placement, Thompson actor witness and A₆ exclusion remain inputs for the
parent's source assembly; this module proves the selection step only.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, ordinary A₇ paragraph, printed p.932 (PDF p.949).
-/

public section
open scoped commutatorElement
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
variable {G : Type*} [Group G] [Finite G]

private theorem six_quasisimple : IsQuasisimple (alternatingGroup (Fin 6)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

omit [Finite G] in
private theorem normal_dichotomy (Q : Subgroup G) [Q.Normal]
    [IsSimpleGroup (G ⧸ Q)] (hQ : IsPGroup 2 Q) (hp : IsPPerfect 2 G)
    (N : Subgroup G) [N.Normal] : N ≤ Q ∨ N = ⊤ := by
  let q := QuotientGroup.mk' Q
  have hn : (N.map q).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with hz | ht
  · exact Or.inl (by simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz)
  · right
    have hs : N ⊔ Q = ⊤ := by
      have hh := congrArg (Subgroup.comap q) ht
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
    exact hp N inferInstance (isPGroup_quotient_of_sup_eq_top N Q hQ hs)

/-- Restrict the actual local-family data to the normalized replacement. -/
private theorem local_family (K B L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) (hBK : B ≤ K)
    (hn : Tv T v ≤ normalizer (B : Set G)) (hp : IsPPerfect 2 B)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) :
    B ∈ CFSG.Quasithin.Chapter1.LIn (Gv v) (Tv T v) := by
  let : IsQuasisimple (alternatingGroup (Fin 6)) := six_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  let H := B ⊔ Tv T v
  have hBH : B ≤ H := le_sup_left
  let eB : B.subgroupOf H ≃* B := subgroupOfEquivOfLe hBH
  let : (B.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr (sup_le B.le_normalizer hn)
  let : IsQuasisimple (B.subgroupOf H ⧸ pCore 2 (B.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).symm
  have hc : (B.subgroupOf H).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : (B.subgroupOf H).Normal).isSubnormal
      (hp.of_surjective eB.symm.toMonoidHom eB.symm.surjective)
  have hjoin : H ≤ K ⊔ Tv T v := sup_le_sup_right hBK _
  have hcore : (K ⊔ Tv T v).pCoreIn 2 ≤ H.pCoreIn 2 := by
    obtain ⟨P, hP⟩ := hK.1.2.2.1
    have hs : (K ⊔ Tv T v).pCoreIn 2 ≤ Tv T v := (pCoreIn_le_sylow _ P).trans hP.le
    exact (le_inf (hs.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hjoin)
  exact ⟨hBK.trans hK.1.1, hc, hK.1.2.2.1.restrict le_sup_right hjoin,
    fun hz => hK.1.2.2.2 (bot_unique (hcore.trans hz.le))⟩

omit [Finite G] in
/-- A single nontrivial quotient actor forces the full commutator identity. -/
private theorem generation (B J : Subgroup G)
    (hn : J ≤ normalizer (B : Set G)) (hp : IsPPerfect 2 B)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hw : ∃ j ∈ J, ∃ b ∈ B, ⁅j, b⁆ ∉ B.pCoreIn 2) : ⁅B, J⁆ = B := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hCB : ⁅B, J⁆ ≤ B := le_normalizer_iff_commutator_le_left.mp hn
  let C := ⁅B, J⁆.subgroupOf B
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer hCB).mpr
    (normalizer_commutator_ge_left B J)
  rcases normal_dichotomy (pCore 2 B) pCore_isPGroup hp C with hc | hc
  · obtain ⟨j, hj, b, hb, hw⟩ := hw
    have hm : ⁅j, b⁆ ∈ ⁅B, J⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hj hb
    exact (hw (mem_map.mpr ⟨⟨⁅j, b⁆, hCB hm⟩, hc hm, rfl⟩)).elim
  · have hh := congrArg (Subgroup.map B.subtype) hc
    simpa only [C, map_subgroupOf_eq_of_le hCB, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- Movement of the seed forces the star kernel into the intrinsic two-core. -/
private theorem star_quotient (B : Subgroup G) (z v : G) (hB : B ≤ Gv v)
    (hp : IsPPerfect 2 B) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hm : ¬ B ≤ centralizer ({z} : Set G)) :
    Nonempty ((starImage z v B ⧸ pCore 2 (starImage z v B)) ≃* alternatingGroup (Fin 6)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  let f := starImageMap z v B hB
  have hk : f.ker ≤ pCore 2 B := by
    rcases normal_dichotomy (pCore 2 B) pCore_isPGroup hp f.ker with h | h
    · exact h
    · exfalso
      apply hm
      intro b hb
      have hh : (⟨b, hb⟩ : B) ∈ f.ker := h.symm ▸ mem_top _
      rw [starImageMap_ker] at hh
      exact centralizer_le (Set.singleton_subset_iff.mpr (z_mem_Uv z v)) hh
  exact ⟨(MonoidHom.quotientPCoreEquivOfSurjective f
    (starImageMap_surjective z v B hB) (pCore_isPGroup.to_le hk)).symm.trans e⟩

/-- A normalized two-perfect A₆ lift belongs to the literal Y_z family as
soon as a Thompson actor acts nontrivially modulo its two-core. -/
theorem mem_Yz_of_alternatingSix_quotient
    (K B L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) (hBK : B ≤ K) (hLB : Lv L v ≤ B)
    (hn : Tv T v ≤ normalizer (B : Set G)) (hp : IsPPerfect 2 B)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hz : ⁅zpowers z, B⁆ ≠ ⊥)
    (hw : ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
      ∃ b ∈ B, ⁅j, b⁆ ∉ B.pCoreIn 2) : B ∈ Yz L T z v := by
  have hB : B ≤ Gv v := hBK.trans hK.1.1
  have hm : ¬ B ≤ centralizer ({z} : Set G) := by
    intro hc
    apply hz
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    simpa only [zpowers_eq_closure, centralizer_closure] using hc
  have hlocal := local_family K B L T z v hK hBK hn hp e
  obtain ⟨es⟩ := star_quotient B z v hB hp e hm
  let : IsQuasisimple (alternatingGroup (Fin 6)) := six_quasisimple
  have hq : IsQuasisimple (starImage z v B ⧸ pCore 2 (starImage z v B)) :=
    IsQuasisimple.of_mulEquiv es.symm
  have hJ : Stellmacher.elementaryAbelianMaxJ (Tv T v) ≤ Tv T v :=
    sSup_le fun _ h => h.1
  have hg := generation B _ (hJ.trans hn) hp e hw
  have hsn := ComponentElimination.Source.starImage_normalizes_of_normalizes (Tv T v) B z v hB hn
  have hsl := ComponentElimination.Source.starImage_normalizes_of_normalizes (Lv L v) B z v hB
    (hLB.trans B.le_normalizer)
  have hs : conjugateSpanBy (starImage z v B) (starImage z v (Tv T v)) =
      starImage z v B :=
    le_antisymm (conjugateSpanBy_le le_rfl hsn) (le_conjugateSpanBy _ _)
  have hres : pResidual 2 (starImage z v B) = ⊤ :=
    (pResidual_eq_top_iff 2 _).mpr
      (hp.of_surjective _ (starImageMap_surjective z v B hB))
  have hne : starImage z v B ≠ ⊥ := by
    intro he
    exact hm (((starImage_eq_bot_iff z v B hB).mp he).trans
      (centralizer_le (Set.singleton_subset_iff.mpr (z_mem_Uv z v))))
  have hcomm : ⁅starImage z v B,
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ = starImage z v B := by
    have he : ⁅B, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆.subgroupOf (Gv v) =
        ⁅B.subgroupOf (Gv v),
          (Stellmacher.elementaryAbelianMaxJ (Tv T v)).subgroupOf (Gv v)⁆ := by
      apply map_injective (Gv v).subtype_injective
      rw [map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans
          (sup_le hB (hJ.trans inf_le_right))), map_commutator,
        map_subgroupOf_eq_of_le hB, map_subgroupOf_eq_of_le (hJ.trans inf_le_right)]
    unfold starImage
    rw [← map_commutator, ← he, hg]
  refine ⟨hlocal, hq, ?_⟩
  rw [hs]
  refine ⟨⟨sup_le hsl hsn, ?_, hne, hcomm⟩, ?_⟩
  · rw [hres, ← MonoidHom.range_eq_map, range_subtype]
  · intro hc
    apply hm
    intro b hb
    apply hc
    exact mem_map.mpr ⟨⟨b, hB hb⟩, mem_map.mpr ⟨⟨b, hB hb⟩, hb, rfl⟩, rfl⟩

/-- The residual lift constructed from the source normalizer placement belongs
to the genuine Y_z family. The earlier Thompson/Baumann argument still supplies
the placement and actor witness; neither is asserted here. -/
theorem replacement_mem_Yz
    (K L T S : Subgroup G) (z v : G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7)
    (hK : K ∈ Yz L T z v)
    (hLv : Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype)
    (hN : K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e x)
    (hT : Tv T v ≤ normalizer (ambientPreimage K e x : Set G))
    (hz : ⁅zpowers z, Lv L v⁆ ≠ ⊥)
    (hw : ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
      ∃ b ∈ replacement K e x, ⁅j, b⁆ ∉ (replacement K e x).pCoreIn 2) :
    replacement K e x ∈ Yz L T z v := by
  obtain ⟨hLB, hBK, hn, hm, ⟨e₆⟩⟩ := replacement_spec K e x L T S z v hLv hN hT hz
  exact mem_Yz_of_alternatingSix_quotient K (replacement K e x) L T z v hK hBK hLB
    hn (replacement_twoPerfect K e x) e₆ hm hw

/-- Conditional reduction of the ordinary A₇ replacement to an A₆ exclusion
for actual Y_z members. The source assembly owner must prove that exclusion
and the displayed normalizer placement and Thompson actor premises. -/
theorem false_of_replacement_and_alternatingSix_exclusion
    (K L T S : Subgroup G) (z v : G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7)
    (hK : K ∈ Yz L T z v)
    (hLv : Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype)
    (hN : K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e x)
    (hT : Tv T v ≤ normalizer (ambientPreimage K e x : Set G))
    (hz : ⁅zpowers z, Lv L v⁆ ≠ ⊥)
    (hw : ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
      ∃ b ∈ replacement K e x, ⁅j, b⁆ ∉ (replacement K e x).pCoreIn 2)
    (hSix : ∀ B ∈ Yz L T z v,
      ¬ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) : False :=
  hSix (replacement K e x) (replacement_mem_Yz K L T S z v e x hK hLv hN hT hz hw)
    ⟨replacementQuotientEquiv K e x⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
