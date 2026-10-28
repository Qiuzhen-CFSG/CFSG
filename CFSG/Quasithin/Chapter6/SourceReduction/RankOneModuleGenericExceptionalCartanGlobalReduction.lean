module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartan
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.PCoreImage

/-!
# Zero-core reductions in the Cartan local-to-global argument

The literal residual K = O²(H) escapes the original maximal local group.
Characteristic two passes from H to this relatively normal subgroup,
so its two-core is nontrivial. Consequently, a subgroup D normalizing K
has O₂(⟨D,H⟩) nontrivial. With local Cartan control this gives exactly the
equivalence used in the first paragraph of 5.2.2.

A generating family for the Cartan must contain an escaping member.
The source 5.1.6 reduction supplies a more specific decomposition, and
the final theorem selects an actual order-three or order-five subgroup
with trivial generated two-core. Construction of that decomposition
and elimination of the selected actor remain separate source obligations.

Source: Aschbacher--Smith, 5.2.2, printed pp.646--649, especially p.647.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The residual's core is nontrivial for the actual outside H-star subgroup.
Only relative normality in H, not ambient normality, is used. -/
theorem residual_core_ne_bot_of_hstar
    {T : Sylow 2 G} {H M : Subgroup G}
    (he : IsEvenCharacteristicAt T)
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    (residual H).pCoreIn 2 ≠ ⊥ := by
  have hR : residual H ≠ ⊥ := by
    intro hb
    exact residual_not_le T H M hH.1.1.2 hTM hH.1.2 (hb ▸ bot_le)
  have hHe : H ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T he hH.1.1
  have hRH : residual H ≤ H := map_subtype_le _
  have hn : ((residual H).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_residual H)
  have hRe : residual H ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hHe hR hRH hn.isSubnormal
  intro hc
  apply hR
  apply bot_unique
  change residual H ⊓ centralizer ((residual H).pCoreIn 2 : Set G) ≤
    (residual H).pCoreIn 2 at hRe
  have hcentral : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
  simpa only [hc, hcentral, inf_top_eq] using hRe

omit [Finite G] in
/-- A normalizer of the residual also normalizes its nontrivial two-core,
which lies in the two-core of the literal generated subgroup. -/
theorem core_ne_bot_of_normalizes_residual {D H : Subgroup G}
    (hR : (residual H).pCoreIn 2 ≠ ⊥)
    (hD : D ≤ normalizer (residual H : Set G)) :
    (D ⊔ H).pCoreIn 2 ≠ ⊥ := by
  have hc := pCoreIn_mono_of_normalizes (p := 2)
    ((map_subtype_le (pResidual 2 H)).trans (show H ≤ D ⊔ H from le_sup_right))
    (sup_le hD (le_normalizer_residual H))
  exact fun he => hR (bot_unique (he ▸ hc))

omit [Finite G] in
/-- The equivalence at the start of 5.2.2, conditional on local control. -/
theorem CartanLocalControl.core_ne_bot_iff {A H D : Subgroup G}
    (h : CartanLocalControl A H) (hR : (residual H).pCoreIn 2 ≠ ⊥)
    (hDA : D ≤ A) :
    (D ⊔ H).pCoreIn 2 ≠ ⊥ ↔ D ≤ normalizer (residual H : Set G) :=
  ⟨h D hDA, core_ne_bot_of_normalizes_residual hR⟩

omit [Finite G] in
/-- Every escaping Cartan subgroup belongs to the source zero-core family. -/
theorem CartanLocalControl.core_eq_bot_of_not_normalizes {A H D : Subgroup G}
    (h : CartanLocalControl A H) (hDA : D ≤ A)
    (hn : ¬ D ≤ normalizer (residual H : Set G)) :
    (D ⊔ H).pCoreIn 2 = ⊥ := by
  by_contra hc
  exact hn (h D hDA hc)

omit [Finite G] in
/-- Any family generating an escaping Cartan contains a zero-core actor. -/
theorem CartanLocalControl.exists_generator_escape {A H : Subgroup G}
    (h : CartanLocalControl A H) (hn : ¬ A ≤ normalizer (residual H : Set G))
    (Δ : Set (Subgroup G)) (hΔ : sSup Δ = A) :
    ∃ D ∈ Δ, (D ⊔ H).pCoreIn 2 = ⊥ ∧
      ¬ D ≤ normalizer (residual H : Set G) := by
  classical
  have he : ∃ D ∈ Δ, ¬ D ≤ normalizer (residual H : Set G) := by
    by_contra hh
    apply hn
    rw [← hΔ]
    apply sSup_le
    intro D hD
    by_contra hDN
    exact hh ⟨D, hD, hDN⟩
  obtain ⟨D, hD, hDN⟩ := he
  exact ⟨D, hD, h.core_eq_bot_of_not_normalizes (hΔ ▸ le_sSup hD) hDN, hDN⟩

/-- The consequence of 5.1.6 used by 5.2.2. The first factor is allowed
to be nontrivial (the order-seventeen factor in degree eight). This is
an output contract, not an asserted source theorem. -/
def CartanSmallGeneration (A H : Subgroup G) (n : ℕ) : Prop :=
  (n = 2 ∨ n = 4 ∨ n = 8) ∧
    ∃ A₀ A₃ A₅ : Subgroup G,
      A₀ ⊔ A₃ ⊔ A₅ = A ∧ (A₀ ⊔ H).pCoreIn 2 ≠ ⊥ ∧
      (A₃ = ⊥ ∨ Nat.card A₃ = 3) ∧ (A₅ = ⊥ ∨ Nat.card A₅ = 5)

/-- The actual order-three or order-five subgroup selected on p.647.
No assertion about an unattached group-family label is used. -/
structure CartanPrimeActor (A H : Subgroup G) (p : ℕ) (D : Subgroup G) : Prop where
  prime : p = 3 ∨ p = 5
  le_cartan : D ≤ A
  card : Nat.card D = p
  zero_core : (D ⊔ H).pCoreIn 2 = ⊥

omit [Finite G] in
/-- The small-Cartan decomposition and local control select a literal
prime-order subgroup whose join with H has trivial two-core. -/
theorem CartanSmallGeneration.exists_prime_actor {A H : Subgroup G} {n : ℕ}
    (hs : CartanSmallGeneration A H n) (h : CartanLocalControl A H)
    (hn : ¬ A ≤ normalizer (residual H : Set G)) :
    ∃ (p : ℕ) (D : Subgroup G), CartanPrimeActor A H p D := by
  classical
  obtain ⟨_, A₀, A₃, A₅, hsup, hcore, h3, h5⟩ := hs
  have h0A : A₀ ≤ A := hsup ▸ le_sup_left.trans le_sup_left
  have h3A : A₃ ≤ A := hsup ▸ le_sup_right.trans le_sup_left
  have h5A : A₅ ≤ A := hsup ▸ le_sup_right
  have h0N := h A₀ h0A hcore
  by_cases h3N : A₃ ≤ normalizer (residual H : Set G)
  · have h5N : ¬ A₅ ≤ normalizer (residual H : Set G) := by
      intro hh
      exact hn (hsup ▸ sup_le (sup_le h0N h3N) hh)
    have hcard : Nat.card A₅ = 5 := h5.resolve_left (fun he => h5N (he ▸ bot_le))
    exact ⟨5, A₅, Or.inr rfl, h5A, hcard,
      h.core_eq_bot_of_not_normalizes h5A h5N⟩
  · have hcard : Nat.card A₃ = 3 := h3.resolve_left (fun he => h3N (he ▸ bot_le))
    exact ⟨3, A₃, Or.inl rfl, h3A, hcard,
      h.core_eq_bot_of_not_normalizes h3A h3N⟩

/-- Source application of the core equivalence, discharging nontriviality
of O₂(O²(H)) from the unchanged generic hypotheses. -/
theorem Input.cartan_core_ne_bot_iff {κ : GroupClass}
    {T : Sylow 2 G} {L W H A D : Subgroup G} {n : ℕ}
    (hs : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hc : CartanLocalControl A H) (hDA : D ≤ A) :
    (D ⊔ H).pCoreIn 2 ≠ ⊥ ↔ D ≤ normalizer (residual H : Set G) :=
  hc.core_ne_bot_iff
    (residual_core_ne_bot_of_hstar (hs.qtke.evenCharacteristic T)
      hs.sylow_normalizes hH) hDA

/-- A selected prime actor genuinely moves the literal residual. This is
the input used after forming G₀ in the changed-Sylow branch. -/
theorem Input.prime_actor_not_normalizes {κ : GroupClass}
    {T : Sylow 2 G} {L W H A D : Subgroup G} {n p : ℕ}
    (hs : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : CartanPrimeActor A H p D) :
    ¬ D ≤ normalizer (residual H : Set G) := by
  intro hD
  exact core_ne_bot_of_normalizes_residual
    (residual_core_ne_bot_of_hstar (hs.qtke.evenCharacteristic T)
      hs.sylow_normalizes hH) hD hd.zero_core

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
