module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Normalizers
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# Thompson normalizer control in Γ₀

Source: Aschbacher–Smith 2.3.8(5a), printed p.524. The central omega subgroup
of an extending Sylow subgroup is nontrivial and lies in J(S), by the
elementary Thompson centralizer theorem underlying B.2.3(7). Thus J(S)
belongs to S₂e by 1.1.4(3). A normalizer outside M would provide a new local
pair based on S, contradicting the normalizer condition and Γ₀ maximality.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

omit [Finite G] in
private theorem thompson_normalizer (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (elementaryAbelianMaxJ A : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change A.map (MulAut.conj x).toMonoidHom = A at hx
  change (elementaryAbelianMaxJ A).map (MulAut.conj x).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj x) A, hx]

/-- The local Thompson subgroup has characteristic-two ambient normalizer. -/
theorem gammaZero_thompson_mem_S2e {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ∈ Chapter1.S2e G := by
  let A := (S : Subgroup H).map H.subtype
  let J := elementaryAbelianMaxJ A
  have hJA : J ≤ A := sSup_le fun _ ha => ha.1
  have hAb := beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)
  obtain ⟨R, _, hAR, hZA, hZC⟩ := lemma_2_3_9_3 T hTM hunique
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)) hH hpair S hUS
  have hRne : (R : Subgroup G) ≠ ⊥ := fun hr => hAb.1.1 (bot_unique (hr ▸ hAR.le))
  let : Nontrivial (R : Subgroup G) := (R : Subgroup G).nontrivial_iff_ne_bot.mpr hRne
  let : Nontrivial (center (R : Subgroup G)) := R.isPGroup'.center_nontrivial
  have hdiv : 2 ∣ Nat.card (center (R : Subgroup G)) :=
    (R.isPGroup'.to_subgroup (center (R : Subgroup G))).card_eq_or_dvd.resolve_left
      (Nat.ne_of_gt Finite.one_lt_card)
  let E := omegaOneCenterAmbient (R : Subgroup G)
  let : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  have hEZ : E ≤ (center (R : Subgroup G)).map (R : Subgroup G).subtype :=
    map_mono (map_subtype_le _)
  have hEne : E ≠ ⊥ := by
    intro he
    exact omega₁_map_subtype_ne_bot (center (R : Subgroup G)) 2 hdiv
      ((map_eq_bot_iff_of_injective _ (R : Subgroup G).subtype_injective).mp he)
  have hEJ : E ≤ J := by
    have hb := elementary_centralizer_maxJ_le_omegaCenter A E (hEZ.trans hZA)
      ((hEZ.trans hZC).trans (centralizer_le hJA))
    intro x hx
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hb hx)).1
  apply Chapter1.lemma_1_1_4_3 R (hG.evenCharacteristic R)
    (fun hj => hEne (bot_unique (hj ▸ hEJ))) ((S.isPGroup'.map H.subtype).to_le hJA)
  intro he
  exact hEne (bot_unique (he ▸ le_inf hEZ hEJ))

/-- Lemma 2.3.8(5a): the full ambient normalizer of J(S) is contained in M. -/
theorem lemma_2_3_8_5a {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    normalizer (elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) : Set G) ≤ M := by
  by_contra hout
  let A := (S : Subgroup H).map H.subtype
  let J := elementaryAbelianMaxJ A
  let N := normalizer (J : Set G)
  have hJ := gammaZero_thompson_mem_S2e hG T hM hTM hunique hH hpair S hUS
  have hcore : twoCore N ≠ ⊥ := fun hn => hJ.1 (bot_unique
    (hn ▸ le_pCoreIn_of_normalizes hJ.2.1 J.le_normalizer le_rfl))
  have hp : (A, N) ∈ localPairs (Chapter1.He G) M :=
    ⟨beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype), hJ.2.2, hcore,
      A.le_normalizer.trans (thompson_normalizer A), hout⟩
  exact gammaZero_full_base_normalizer_not_le T hTM hunique hH S
    (localPair_snd_mem_gamma hp) ⟨N, hp, le_rfl⟩ (thompson_normalizer A)

end CFSG.Quasithin.Chapter2
