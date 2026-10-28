module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicField
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalDegreeEight
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSpecialLinearResidual
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LinearThreePrimeRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SpecialLinearThreeLocalQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicField

/-!
# Comparing the selected parabolic and the original residual field

A full Sylow of the original residual witnesses locality of the selected
right factor. Local-component minimality preserves its proper image modulo
the residual two-core. The projective and special-linear point/line
placement theorems identify its intrinsic quotient with PSL₂ over the
residual field. Together with the symplectic comparison, this proves equality
of the selected and residual degrees in all three classical rank-two rows.

The comparison discharges the residual-degree premise in the existing SL₃
and Sp₄ normalization arguments for original left degree two, four or eight,
when that degree divides the selected right degree. In the smaller changed
Sylow branch, a rank-two containing component forces the right section to
be PSL₂(8), hence forces the original residual degree to be three. Thus an
even residual degree excludes this entire containing family, including the
binary triality endpoint. The original degree of L remains separate.

The internal import reuses the field-comparison proof within this Cartan
module family while preserving its existing private boundary. Source
selection, the higher-field reduction, zero-core models and the remaining
changed-Sylow branches remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith A.3.12, 5.1.10 and 5.2.2,
printed pp.47–48,634,648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem local_quotient_of_cover
    {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (S : Sylow 2 X) {R : Subgroup X}
    (hR : R ∈ ChapterA.Section03.localCComponents S)
    (htop : (⊤ : Subgroup X).IsCComponent) (hne : R ≠ ⊤)
    (q : X →* Q) (hq : Function.Surjective q) (hk : q.ker = pCore 2 X)
    (hmodel : ∀ (P : Sylow 2 Q) (C : Subgroup Q),
      C ∈ ChapterA.Section03.localCComponents P → C ≠ ⊤ →
      Nonempty ((C ⧸ pCore 2 C) ≃* SL(2,F))) :
    Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,F)) := by
  let : Group.IsNilpotent q.ker := hk ▸ pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hl : R.map q ∈ ChapterA.Section03.localCComponents (S.mapSurjective hq) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hR q
  have hproper : R.map q ≠ ⊤ := by
    intro he
    apply hne
    apply local_cComponent_eq_of_map_eq hR htop le_top q
      (hk ▸ pCore_isPGroup.le_sylow_of_normal S)
    simpa only [map_top_of_surjective q hq] using he
  have hr : IsPGroup 2 (q.subgroupMap R).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  obtain ⟨e⟩ := hmodel (S.mapSurjective hq) (R.map q) hl hproper
  exact ⟨((q.subgroupMap R).quotientPCoreEquivOfSurjective
    (q.subgroupMap_surjective R) hr).trans e⟩

private theorem linear_local_quotient
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {R : Subgroup X}
    (hR : R ∈ ChapterA.Section03.localCComponents S)
    (htop : (⊤ : Subgroup X).IsCComponent) (hne : R ≠ ⊤)
    {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 3 (2 ^ f)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨a⟩ := local_quotient_of_cover S hR htop hne q hq hk
    (ChapterA.Section03.SourceEmbeddings.linear_three_local_core_quotient hF hf)
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨a.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))⟩⟩

private theorem specialLinear_local_quotient
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {R : Subgroup X}
    (hR : R ∈ ChapterA.Section03.localCComponents S)
    (htop : (⊤ : Subgroup X).IsCComponent) (hne : R ≠ ⊤)
    {f : ℕ} (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL (X ⧸ pCore 2 X) 3 (2 ^ f)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨a⟩ := local_quotient_of_cover S hR htop hne q hq hk
    (ChapterA.Section03.SourceEmbeddings.special_linear_three_local_core_quotient hF hf)
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨a.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))⟩⟩

/-- The selected parabolic in a PSL₃ residual has that residual’s coefficient field. -/
theorem LocalData.linear_residual_right_quotient
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  let eK : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eqK := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let : IsQuasisimple ((residual H) ⧸ pCore 2 (residual H)) :=
    IsQuasisimple.of_mulEquiv eqK
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (residual H)) pCore_isPGroup (isPPerfect_embedded_pResidual 2 H)
  obtain ⟨S,_,hl⟩ := d.right_local_in_residual hTH
  have hn : R.subgroupOf (residual H) ≠ ⊤ := fun he => hR.not_ge (subgroupOf_eq_top.mp he)
  have hs := linear_local_quotient S hl ht hn hf
    (show ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H)) 3 (2 ^ f) from
      ⟨F,inferInstance,inferInstance,hF,⟨eqK.symm.trans e⟩⟩)
  let er := subgroupOfEquivOfLe d.right_le_residual
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  exact hs.of_mulEquiv eqr.symm

/-- The same quotient identification in SL₃ preserves the central cover. -/
theorem LocalData.specialLinear_residual_right_quotient
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  let eK : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eqK := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let : IsQuasisimple ((residual H) ⧸ pCore 2 (residual H)) :=
    IsQuasisimple.of_mulEquiv eqK
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (residual H)) pCore_isPGroup (isPPerfect_embedded_pResidual 2 H)
  obtain ⟨S,_,hl⟩ := d.right_local_in_residual hTH
  have hn : R.subgroupOf (residual H) ≠ ⊤ := fun he => hR.not_ge (subgroupOf_eq_top.mp he)
  have hs := specialLinear_local_quotient S hl ht hn hf
    (show Chapter1.Section02.LocalModels.IsSL ((residual H) ⧸ pCore 2 (residual H)) 3 (2 ^ f) from
      ⟨F,inferInstance,inferInstance,hF,⟨eqK.symm.trans e⟩⟩)
  let er := subgroupOfEquivOfLe d.right_le_residual
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  exact hs.of_mulEquiv eqr.symm

/-- The literal right-factor and residual markings have equal degrees in all three rows. -/
theorem LocalData.rankTwo_residual_degree_eq
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f m : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) : f = m := by
  rcases hm with hm | hm | hm
  · exact binary_degree_eq (d.linear_residual_right_quotient hTH hR hf hm) hr
  · exact binary_degree_eq (d.specialLinear_residual_right_quotient hTH hR hf hm) hr
  · exact d.symplectic_residual_degree_eq hTH hR hf hm hr

/-- Normalize the original Cartan using the selected right degree; its residual-degree comparison is proved. -/
theorem LocalData.cartan_normalizes_of_rankTwo_matching_small_degree
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n f m : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hnm : n ∣ m)
    (hR : R < residual H) (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) :
    A ≤ normalizer (residual H : Set G) := by
  have hfm := d.rankTwo_residual_degree_eq hH.1.1.2 hR hf (Or.inr hm) hr
  have hnf : n ∣ f := hfm.symm ▸ hnm
  rcases hm with hm | hm
  · rcases hn with hn | hn | hn
    · exact h.cartan_normalizes_of_specialLinear_residual_small_degree hH c hcontrol (.inl hn) hf hnf hm
    · exact h.cartan_normalizes_of_specialLinear_residual_small_degree hH c hcontrol (.inr hn) hf hnf hm
    · subst n
      exact h.cartan_normalizes_of_specialLinear_residual_degree_eight hH c hcontrol hf hnf hm
  · rcases hn with hn | hn | hn
    · exact h.cartan_normalizes_of_symplectic_residual_small_degree hH hgen c hcontrol (.inl hn) hf hnf hm
    · exact h.cartan_normalizes_of_symplectic_residual_small_degree hH hgen c hcontrol (.inr hn) hf hnf hm
    · subst n
      exact h.cartan_normalizes_of_symplectic_residual_degree_eight hH hgen c hcontrol hf hnf hm

/-- The escaping prime actor supplies strictness in the actual nonzero-core configuration. -/
theorem LocalData.rankTwo_prime_excluded_of_matching_small_degree
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p f m : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hnm : n ∣ m)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) : False :=
  h.prime_actor_not_normalizes hH hd (hd.le_cartan.trans
    (d.cartan_normalizes_of_rankTwo_matching_small_degree h hH hgen c hcontrol hn hnm
      (d.right_lt_residual hH.1.1.2 c hd hz) hf hm hr))

/-- The surviving binary triality container forces degree three for the original classical residual. -/
theorem LocalData.source_rankTwo_container_residual_degree_three
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hmodel : Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K))
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    f = 3 ∧ p = 3 := by
  obtain ⟨_,hr,hp⟩ := d.source_overcomponent_rankTwo_configuration
    h hH c hd hz hSyl hRK hKX hK hKn hmodel
  exact ⟨d.rankTwo_residual_degree_eq hH.1.1.2
    (d.right_lt_residual hH.1.1.2 c hd hz) hf hm (m := 3) hr,hp⟩

/-- An even original residual degree excludes every rank-two containing component at the smaller Sylow. -/
theorem LocalData.source_not_rankTwo_container_of_even_residual_degree
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hf : 1 < f) (heven : Even f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) := by
  intro hmodel
  have he := (d.source_rankTwo_container_residual_degree_three
    h hH c hd hz hSyl hRK hKX hK hKn hmodel hf hm).1
  rw [he] at heven
  exact (by decide : ¬ Even 3) heven

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
