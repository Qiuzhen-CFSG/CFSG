module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeMovedComponentActualPair
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSevenFixed

/-!
# The original component branch after changed-Sylow maximality

For a right factor which is an actual C-component of H, its original
full-Sylow local membership follows from H∈H(T). Thus source 1.2.8(3)
applies to precisely this factor. In the non-A₅ row it makes T₀=N_T(R)
Sylow in G₀T₀B, removing the ambient larger-Sylow alternative from every
subsequent component sieve. The selected overcomponent is normal in the
literal G₀T₀, and the marked quotient embedding remains strict.

This is the component choice in source 5.1.10(1), used in 5.2.2,
printed pp.634 and 648. The diagram-parabolic choice has a different
original C-component; it is not asserted to satisfy the component input
of the theorems here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An actual right C-component of H belongs to the original full-Sylow
family, rather than only the smaller N_T(R)-family. -/
theorem LocalData.right_mem_original_local_family
    {T : Sylow 2 G} {L H B D R : Subgroup G}
    (d : LocalData T L H B D R)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hC : (R.subgroupOf H).IsCComponent) :
    R ∈ Chapter1.L G (T : Subgroup G) := by
  exact Chapter1.mem_L_of_cComponent hH.1
    ⟨T.subtype hH.2, map_subgroupOf_eq_of_le hH.2⟩
    (d.right_le_residual.trans (map_subtype_le _)) hC

/-- At a non-A₅ original right C-component the actual normalizing Sylow is
Sylow in the full local extension. No Sylow equality is an extra premise. -/
theorem LocalData.normalizingSylow_sylow_extension_of_component
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    Chapter1.IsSylowIn 2 (normalizingSylow T R) (extension T L H B D R) := by
  obtain ⟨P,hTP,_⟩ := d.exists_changedSylow hH.1.1.2 c hd hz
  exact ⟨P,d.changedSylow_eq_of_nonA5 h hH c hd hz
    (d.right_mem_original_local_family hH.1.1 hC) hnot P hTP⟩

/-- The same normalizing Sylow is Sylow in the smaller source join G₀T₀. -/
theorem LocalData.normalizingSylow_sylow_source_of_component
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R) :=
  (d.normalizingSylow_sylow_extension_of_component h hH c hd hz hC hnot).restrict
    le_sup_right le_sup_left

/-- For an original non-A₅ component, the actual smaller-Sylow sieve is
unconditional: the larger ambient-Sylow alternative has been eliminated.
The binary triality endpoint retains its literal right quotient and actor. -/
theorem LocalData.component_source_overcomponent_configuration
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    let X := generated L H D R ⊔ normalizingSylow T R
    let q := QuotientGroup.mk' (pCore 2 X)
    ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
      (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
      (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
      ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
      (∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ k))) ∧
      (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
        Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
        ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3) := by
  have hSyl := d.normalizingSylow_sylow_source_of_component h hH c hd hz hC hnot
  obtain ⟨K,hRK,hKX,hK,hKn,hlt,hb,_,hternary,hrank⟩ :=
    d.source_overcomponent_small_exclusions h hH c hd hz hSyl
  exact ⟨K,hRK,hKX,hK,hKn,hlt,hb,hternary,
    d.source_overcomponent_rankTwo_configuration h hH c hd hz hSyl hRK hKX hK hKn⟩


/-- A proper containing odd-prime PSL₂ quotient would force the original
right factor to have the A₅ quotient. -/
theorem LocalData.source_overcomponent_not_primePSL2
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n q : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hq : q.Prime) (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q := by
  intro hm
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  have hl : R.subgroupOf X ∈ ChapterA.Section03.localCComponents S := by
    rw [heS]
    exact ((Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp
      ⟨hRX,d.right_mem_local_family h hH⟩).1
  let eR := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hRX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hRX))
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  have he := Chapter1.Section02.MovedMaximality.eq_of_primePSL2_quotient S hl hK
    (comap_mono hRK.le) (fun hh => hnot (hh.of_mulEquiv eR.symm)) hq ho
    (hm.of_mulEquiv eK)
  have hh := congrArg (map X.subtype) he
  rw [map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hKX] at hh
  exact hRK.ne hh

/-- For an actual moved original component, the J₁ containing quotient
is excluded by the four-model theorem on that same original factor. -/
theorem LocalData.component_source_overcomponent_not_janko
    {T : Sylow 2 G} {L W H A B D R X K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  have hlocal := d.right_mem_original_local_family hH.1.1 hC
  have hmove : R < conjugateSpanBy R (T : Subgroup G) := by
    rw [←d.residual_eq_conjugateSpan]
    exact d.right_lt_residual hH.1.1.2 c hd hz
  have hmodel := Chapter1.Section02.MovedMaximality.moved_local_model h.qtke T hlocal hmove
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  have hl : R.subgroupOf X ∈ ChapterA.Section03.localCComponents S := by
    rw [heS]
    exact ((Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp
      ⟨hRX,d.right_mem_local_family h hH⟩).1
  let eR := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hRX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hRX))
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  have he := Chapter1.Section02.MovedMaximality.eq_of_janko_quotient S hl hK
    (comap_mono hRK.le) (hmodel.of_mulEquiv eR)
    (fun hh => hnot (hh.of_mulEquiv eR.symm)) (eK.trans e)
  have hh := congrArg (map X.subtype) he
  rw [map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hKX] at hh
  exact hRK.ne hh


/-- The original component branch carries both odd rank-one exclusions
alongside the rank-two binary endpoint, on the same containing component. -/
theorem LocalData.component_source_overcomponent_odd_exclusions
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    let X := generated L H D R ⊔ normalizingSylow T R
    let q := QuotientGroup.mk' (pCore 2 X)
    ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
      (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
      (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
      ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
      (∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
        Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ k))) ∧
      (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
        Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
        ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3) ∧
      (∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q) ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  have hSyl := d.normalizingSylow_sylow_source_of_component h hH c hd hz hC hnot
  obtain ⟨K,hRK,hKX,hK,hKn,hlt,hb,hternary,hrank⟩ :=
    d.component_source_overcomponent_configuration h hH c hd hz hC hnot
  have hRX : R ≤ generated L H D R ⊔ normalizingSylow T R :=
    le_sup_left.trans (le_sup_right.trans le_sup_left)
  exact ⟨K,hRK,hKX,hK,hKn,hlt,hb,hternary,hrank,
    fun _ hq ho => d.source_overcomponent_not_primePSL2 h hH hSyl hRX hKX hRK hK hnot hq ho,
    d.component_source_overcomponent_not_janko h hH c hd hz hC hnot hSyl hRX hKX hRK hK⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
