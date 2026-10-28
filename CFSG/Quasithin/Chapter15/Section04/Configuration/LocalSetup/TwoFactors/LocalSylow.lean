module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Transfer
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.CharacteristicLocalSylow
public import Stellmacher.BaumannMap

/-!
# Sylow promotion in the mixed-factor construction

For `Baum(T) ≤ Tᵢ ≤ T`, Baumann heredity and the universal normalizer bound
of 15.4.16 put `N_G(Tᵢ)` in the relevant maximal two-local subgroup. The
characteristic-normalizer Sylow criterion then promotes `Tᵢ` from its local
centralizer to `C_G(E₀)`. Restriction gives the prescribed Sylow subgroup of
each intermediate group, and the proved 15.4.17(1) supplies the hypotheses
of 1.1.5 with the same centralizer and central involutions.

The local Sylow witness and the nontrivial subgroup `E₀` still have to be
constructed from the mixed factors. Neither the promoted Sylow conclusion
nor a generalized-Fitting classification is an input to these lemmas.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the third and fourth paragraphs of 15.4.18,
printed p.1162.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Distinct unique maximal two-local overgroups force a trivial two-core
in the generated group. This supplies the core hypothesis in 15.4.15 before
applying F.6.5; normality is used only inside the generated group. -/
theorem twoCore_join_eq_bot_of_distinct_unique {A B M₁ M₂ : Subgroup G}
    (hA : ∀ M : Subgroup G, IsMaximalTwoLocal M → A ≤ M → M = M₁)
    (hB : ∀ M : Subgroup G, IsMaximalTwoLocal M → B ≤ M → M = M₂)
    (hne : M₁ ≠ M₂) : pCore 2 (A ⊔ B : Subgroup G) = ⊥ := by
  let I := A ⊔ B
  have hR : I.pCoreIn 2 = ⊥ := by
    by_contra hR
    have hn : I ≤ normalizer (I.pCoreIn 2 : Set G) := by
      simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
        using (pCore 2 I).le_normalizer_map I.subtype
    obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal
      (show IsTwoLocal (normalizer (I.pCoreIn 2 : Set G)) from
        ⟨I.pCoreIn 2, hR, isPGroup_pCoreIn 2 I, rfl⟩)
    exact hne ((hA M hM (le_sup_left.trans (hn.trans hNM))).symm.trans
      (hB M hM (le_sup_right.trans (hn.trans hNM))))
  exact ((pCore 2 I).map_eq_bot_iff_of_injective I.subtype_injective).mp hR

/-- The mixed local cores differ when the first is normalized by `Y₁T`.
If they coincided, their two-local normalizer would contain both `Y₁T` and
`XT = ⟨Y₂,T⟩`, contradicting the two distinct unique overgroups. -/
theorem mixed_twoCores_ne {Y₁ Y₂ X T Tᵢ M₁ M₂ : Subgroup G}
    (hgen : Y₂ ⊔ T = X ⊔ T)
    (h₁ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁ ⊔ T ≤ M → M = M₁)
    (h₂ : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hcore : (Y₁ ⊔ Tᵢ).pCoreIn 2 ≠ ⊥)
    (hnorm : Y₁ ⊔ T ≤ normalizer ((Y₁ ⊔ Tᵢ).pCoreIn 2 : Set G)) :
    (Y₁ ⊔ Tᵢ).pCoreIn 2 ≠ (Y₂ ⊔ Tᵢ).pCoreIn 2 := by
  intro heq
  let R := (Y₁ ⊔ Tᵢ).pCoreIn 2
  have hn₂ : Y₂ ⊔ Tᵢ ≤ normalizer (R : Set G) := by
    change Y₂ ⊔ Tᵢ ≤ normalizer ((Y₁ ⊔ Tᵢ).pCoreIn 2 : Set G)
    rw [heq]
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 (Y₂ ⊔ Tᵢ : Subgroup G)).le_normalizer_map (Y₂ ⊔ Tᵢ : Subgroup G).subtype
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (R : Set G)) from
      ⟨R, hcore, isPGroup_pCoreIn 2 (Y₁ ⊔ Tᵢ), rfl⟩)
  have hXM : X ⊔ T ≤ M := by
    rw [← hgen]
    exact (sup_le (le_sup_left.trans hn₂) (le_sup_right.trans hnorm)).trans hNM
  exact hne ((h₁ M hM (hnorm.trans hNM)).symm.trans (h₂ M hM hXM))

/-- Relative index of the supplied ambient image of a Sylow subgroup. -/
theorem prime_not_dvd_sylow_image_relIndex {p : ℕ} [Fact p.Prime]
    {H Q : Subgroup G} (P : Sylow p H)
    (hP : (P : Subgroup H).map H.subtype = Q) : ¬ p ∣ Q.relIndex H := by
  have heq : Q.subgroupOf H = (P : Subgroup H) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  change ¬ p ∣ (Q.subgroupOf H).index
  rw [heq]
  exact P.not_dvd_index

/-- The local Sylow witness, Baumann heredity, and 15.4.16 together construct
the actual Sylow subgroup of `C_G(E₀)`. -/
theorem sylow_centralizer_of_baumann_control (T : Sylow 2 G)
    {Tᵢ M E₀ : Subgroup G} (hTᵢT : Tᵢ ≤ (T : Subgroup G))
    (hSTᵢ : ChapterB.baumann (T : Subgroup G) ≤ Tᵢ)
    (hTᵢC : Tᵢ ≤ centralizer (E₀ : Set G))
    (P : Sylow 2 (M ⊓ centralizer (E₀ : Set G) : Subgroup G))
    (hP : (P : Subgroup (M ⊓ centralizer (E₀ : Set G) : Subgroup G)).map
      (M ⊓ centralizer (E₀ : Set G) : Subgroup G).subtype = Tᵢ)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (h16 : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N →
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ N) :
    ∃ S : Sylow 2 (centralizer (E₀ : Set G)),
      (S : Subgroup (centralizer (E₀ : Set G))).map
        (centralizer (E₀ : Set G)).subtype = Tᵢ ∧
      (T : Subgroup G) ⊓ centralizer (E₀ : Set G) = Tᵢ := by
  let B : Subgroup Tᵢ := ChapterB.baumann ⊤
  let : B.Characteristic := ChapterB.baumann_characteristic
  have hB : B.map Tᵢ.subtype = ChapterB.baumann Tᵢ := by
    simpa only [B, ChapterB.baumann, ChapterB.thompsonAlpha, ← MonoidHom.range_eq_map,
      range_subtype] using Stellmacher.baumann_map_injective Tᵢ.subtype Tᵢ.subtype_injective ⊤
  have hBaum := ChapterB.lemma_B_2_3_4 (T : Subgroup G) Tᵢ hSTᵢ hTᵢT
  have hn : normalizer (B.map Tᵢ.subtype : Set G) ≤ M := by
    rw [hB, ← hBaum]
    exact h16 M hM hTM
  obtain ⟨S, hS⟩ := exists_sylow_of_characteristic_normalizer Tᵢ M
    (centralizer (E₀ : Set G)) B (T.isPGroup'.to_le hTᵢT) hTᵢC
    (prime_not_dvd_sylow_image_relIndex P hP) hn
  refine ⟨S, hS, ?_⟩
  exact (inf_eq_sylow_map S T.isPGroup' (hS ▸ hTᵢT)).trans hS

/-- A nontrivial normal two-subgroup produces membership in the genuine local
family and its SQTK inheritance; no ordinary/generalized Fitting confusion is
involved. -/
theorem sqtk_of_nontrivial_normal_two_subgroup {K : GroupClass}
    (hG : IsSimpleQTKE K G) {B I : Subgroup G}
    (hB : IsPGroup 2 B) (hBne : B ≠ ⊥) (hBI : B ≤ I)
    (hIN : I ≤ normalizer (B : Set G)) : I ∈ Chapter1.H G ∧ IsSQTK K I := by
  have hi : I ∈ Chapter1.H G := by
    intro hb
    exact hBne (le_bot_iff.mp (hb ▸ le_pCoreIn_of_normalizes hB hBI hIN))
  exact ⟨hi, Chapter3.sqtk_of_mem_H hG hi⟩

/-- Apply the actual 15.4.17(1) to the centralizer obtained by Sylow promotion.
The Sylow subgroup of each intermediate `I` has exactly the image `Tᵢ`. -/
theorem local115_from_promoted_centralizer {K : GroupClass}
    (hG : IsQTKE K G) (T : Sylow 2 G)
    {E₀ Tᵢ I : Subgroup G} [IsElementaryAbelian 2 E₀]
    (hE₀ : E₀ ≠ ⊥) (hE₀T : E₀ ≤ (T : Subgroup G))
    (S : Sylow 2 (centralizer (E₀ : Set G)))
    (hS : (S : Subgroup (centralizer (E₀ : Set G))).map
      (centralizer (E₀ : Set G)).subtype = Tᵢ)
    (hTᵢT : Tᵢ ≤ (T : Subgroup G)) (hTᵢI : Tᵢ ≤ I)
    (hIC : I ≤ centralizer (E₀ : Set G))
    {z : G} (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hCM : centralizer ({z} : Set G) ≤ M) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = Tᵢ ∧
      Chapter1.Lemma115Hypotheses I P M z := by
  have hTC : (T : Subgroup G) ⊓ centralizer (E₀ : Set G) = Tᵢ :=
    (inf_eq_sylow_map S T.isPGroup' (hS ▸ hTᵢT)).trans hS
  have hE₀C : E₀ ≤ centralizer (E₀ : Set G) := by
    intro e he
    exact mem_centralizer_iff.mpr fun a ha => setLike_mul_comm ha he
  obtain ⟨P, hP, hp⟩ := lemma_15_4_17_one hG T hE₀ hE₀T hE₀C le_rfl
    (centralizer_le_normalizer (E₀ : Set G)) S (hS.trans hTC.symm)
    (hTC ▸ hTᵢI) hIC hz hz1 hM hCM
  exact ⟨P, hP.trans hTC, hp⟩

/-- Transport both actual symmetric quotients and the prescribed Sylow
intersection into the generated subgroup. The source construction must prove
the intersection equality before this packaging lemma applies. -/
theorem goldschmidt_triple_in_join (G₁ G₂ Tᵢ : Subgroup G)
    (h₁ : Nonempty ((G₁ ⧸ pCore 2 G₁) ≃* Equiv.Perm (Fin 3)))
    (h₂ : Nonempty ((G₂ ⧸ pCore 2 G₂) ≃* Equiv.Perm (Fin 3)))
    (P : Sylow 2 (G₁ ⊔ G₂ : Subgroup G))
    (hP : (P : Subgroup (G₁ ⊔ G₂ : Subgroup G)).map (G₁ ⊔ G₂ : Subgroup G).subtype = Tᵢ)
    (hint : G₁ ⊓ G₂ = Tᵢ) :
    ChapterF.IsGoldschmidtTriple (G₁.subgroupOf (G₁ ⊔ G₂))
      (G₂.subgroupOf (G₁ ⊔ G₂)) := by
  let I := G₁ ⊔ G₂
  have hquot (A : Subgroup G) (hAI : A ≤ I)
      (hq : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((A.subgroupOf I) ⧸ pCore 2 (A.subgroupOf I)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := hq
    let f := subgroupOfEquivOfLe hAI
    exact ⟨(QuotientGroup.congr (pCore 2 (A.subgroupOf I)) (pCore 2 A)
      f (pCore_map_iso 2 f)).trans e⟩
  refine ⟨?_, hquot G₁ le_sup_left h₁, hquot G₂ le_sup_right h₂, P, ?_⟩
  · rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  · change (G₁ ⊓ G₂).subgroupOf I = (P : Subgroup I)
    rw [hint, ← hP]
    exact comap_map_eq_self_of_injective I.subtype_injective _

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
