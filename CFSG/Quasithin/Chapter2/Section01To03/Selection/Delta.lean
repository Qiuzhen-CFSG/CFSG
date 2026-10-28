module

public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Transport
/-!
# Local pairs from maximal members of δ

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.3.3 and the existence assertions following Notations 2.3.4–5,
printed p.522. Throughout, the collection is Chapter 1's actual `He`.

Upward closure of S₂e and maximality of D control the normalizers of all
strict two-overgroups inside M. A Sylow S of N_M(D) strictly contains D:
otherwise the p-group normalizer condition makes D Sylow in M, contrary
to the unique maximal two-local hypothesis. The normalizer barrier then
makes S Sylow in N_G(D), placing its two-core inside M. Maximality of D
identifies that core with D, and characteristic two supplies β's
centralizer clause. The resulting genuine pair (S,N_G(D)) supplies every
required nonempty family. No additional classification input is needed.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M D U : Subgroup G}

omit [Finite G] in
private theorem sylow_image_maximal {H V : Subgroup G} (S : Sylow 2 H)
    (hV : IsPGroup 2 V) (hSV : (S : Subgroup H).map H.subtype ≤ V) (hVH : V ≤ H) :
    V = (S : Subgroup H).map H.subtype := by
  have he := S.is_maximal' (hV.comap_of_injective H.subtype H.subtype_injective)
    (show (S : Subgroup H) ≤ V.subgroupOf H from fun x hx => hSV (mem_map.mpr ⟨x, hx, rfl⟩))
  change V.subgroupOf H = (S : Subgroup H) at he
  have hm := congrArg (map H.subtype) he
  simpa only [map_subgroupOf_eq_of_le hVH] using hm

/-- Maximality in δ controls every strict two-overgroup inside M. -/
theorem deltaStar_strict_overgroup_normalizer (hD : D ∈ deltaStar (Chapter1.He G) M)
    (hU : U ∈ twoSubgroups) (hDU : D < U) (hUM : U ≤ M) :
    normalizer (U : Set G) ≤ M := by
  by_contra hn
  have hDe : D ∈ Chapter1.S2e G := ⟨hD.1.1.1, hD.1.1.2, hD.1.2.1⟩
  have hUe := Chapter1.lemma_1_1_4_1 hDe hDU.le hU.2
  have hUd : U ∈ delta (Chapter1.He G) M := ⟨hU, hUe.2.2, hUM, hn⟩
  exact hDU.not_ge (hD.2 hUd hDU.le)

omit [Finite G] in
private theorem delta_core_ne (hD : D ∈ delta (Chapter1.He G) M) :
    twoCore (normalizer (D : Set G)) ≠ ⊥ := by
  intro he
  exact hD.1.1 (bot_unique (he ▸
    le_pCoreIn_of_normalizes hD.1.2 D.le_normalizer le_rfl))

/-- The p-group normalizer condition gives D < S for S Sylow in N_M(D). -/
theorem deltaStar_sylow_strict (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hD : D ∈ deltaStar (Chapter1.He G) M)
    (S : Sylow 2 ↥(M ⊓ normalizer (D : Set G))) :
    D < (S : Subgroup ↥(M ⊓ normalizer (D : Set G))).map (M ⊓ normalizer (D : Set G)).subtype := by
  let N := M ⊓ normalizer (D : Set G)
  let A := (S : Subgroup N).map N.subtype
  have hDN : D ≤ N := le_inf hD.1.2.2.1 D.le_normalizer
  have hDA : D ≤ A := (le_pCoreIn_of_normalizes hD.1.1.2 hDN inf_le_right).trans
    (pCoreIn_le_sylow N S)
  have hAM : A ≤ M := (map_subtype_le _).trans inf_le_left
  refine lt_of_le_of_ne hDA ?_
  intro he
  obtain ⟨P, hAP⟩ := (S.isPGroup'.map N.subtype).comap_of_injective M.subtype M.subtype_injective |>.exists_le_sylow
  have hAP' : A ≤ (P : Subgroup M).map M.subtype := by
    have hm := map_mono hAP (f := M.subtype)
    change (A.subgroupOf M).map M.subtype ≤ _ at hm
    simpa only [map_subgroupOf_eq_of_le hAM] using hm
  let B := (P : Subgroup M).map M.subtype
  have hDB : D ≤ B := hDA.trans hAP'
  have hBN : B ⊓ normalizer (D : Set G) ≤ N := le_inf
    (inf_le_left.trans (map_subtype_le _)) inf_le_right
  have hinter : B ⊓ normalizer (D : Set G) = D := by
    have hh := sylow_image_maximal S ((P.isPGroup'.map M.subtype).to_le inf_le_left)
      (show A ≤ B ⊓ normalizer (D : Set G) from
        le_inf hAP' ((map_subtype_le _).trans inf_le_right)) hBN
    exact hh.trans he.symm
  let : Group.IsNilpotent B := (P.isPGroup'.map M.subtype).isNilpotent
  have hself : normalizer (D.subgroupOf B : Set B) = D.subgroupOf B := by
    rw [← subgroupOf_normalizer_eq hDB]
    apply le_antisymm
    · intro x hx
      exact hinter ▸ show (x : G) ∈ B ⊓ normalizer (D : Set G) from ⟨x.property, hx⟩
    · exact fun x hx => D.le_normalizer hx
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := B)) _ hself
  have hBD : B ≤ D := subgroupOf_eq_top.mp htop
  exact hD.1.2.2.2 (core_overgroup_le_of_sylow T hTM hunique (delta_core_ne hD.1) P
    (hBD.trans D.le_normalizer))

/-- A Sylow subgroup of N_M(D) is Sylow in the full ambient normalizer N_G(D). -/
theorem deltaStar_sylow_ambient (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hD : D ∈ deltaStar (Chapter1.He G) M)
    (S : Sylow 2 ↥(M ⊓ normalizer (D : Set G))) :
    ∃ R : Sylow 2 (normalizer (D : Set G)),
      (R : Subgroup (normalizer (D : Set G))).map (normalizer (D : Set G)).subtype =
      (S : Subgroup ↥(M ⊓ normalizer (D : Set G))).map (M ⊓ normalizer (D : Set G)).subtype := by
  let N := normalizer (D : Set G)
  let L := M ⊓ N
  let A := (S : Subgroup L).map L.subtype
  have hDA : D < A := deltaStar_sylow_strict T hTM hunique hD S
  have hAL : A ≤ L := map_subtype_le _
  obtain ⟨R, hAR⟩ := (S.isPGroup'.map L.subtype).comap_of_injective N.subtype N.subtype_injective |>.exists_le_sylow
  have hAR' : A ≤ (R : Subgroup N).map N.subtype := by
    have hm := map_mono hAR (f := N.subtype)
    change (A.subgroupOf N).map N.subtype ≤ _ at hm
    simpa only [map_subgroupOf_eq_of_le (hAL.trans inf_le_right)] using hm
  have hRM : (R : Subgroup N).map N.subtype ≤ M := by
    apply p_overgroup_le_of_normalizers_le (R.isPGroup'.map N.subtype) hAR' (hAL.trans inf_le_left)
    intro W hW hAW hWM
    exact deltaStar_strict_overgroup_normalizer hD
      ⟨fun he => hD.1.1.1 (bot_unique (he ▸ hDA.le.trans hAW)), hW⟩
      (hDA.trans_le hAW) hWM
  exact ⟨R, sylow_image_maximal S (R.isPGroup'.map N.subtype) hAR'
    (le_inf hRM (map_subtype_le _))⟩

/-- A maximal member of δ is exactly the two-core of its full normalizer. -/
theorem deltaStar_eq_normalizer_twoCore (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hD : D ∈ deltaStar (Chapter1.He G) M) : D = twoCore (normalizer (D : Set G)) := by
  let N := normalizer (D : Set G)
  let S : Sylow 2 ↥(M ⊓ N) := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := deltaStar_sylow_ambient T hTM hunique hD S
  have hDE : D ≤ twoCore N := le_pCoreIn_of_normalizes hD.1.1.2 D.le_normalizer le_rfl
  have hEM : twoCore N ≤ M :=
    (pCoreIn_le_sylow N R).trans (hR ▸ (map_subtype_le _).trans inf_le_left)
  by_contra he
  have hn := deltaStar_strict_overgroup_normalizer hD
    ⟨delta_core_ne hD.1, isPGroup_pCoreIn 2 N⟩ (lt_of_le_of_ne hDE he) hEM
  exact hD.1.2.2.2 ((le_normalizer_twoCore N).trans hn)

/-- Lemma 2.3.3(1), with the actual characteristic-two collection. -/
theorem deltaStar_strict_overgroup_beta (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hD : D ∈ deltaStar (Chapter1.He G) M)
    (hU : U ∈ twoSubgroups) (hDU : D < U) (hUM : U ≤ M) : U ∈ beta M := by
  refine ⟨hU, hUM, ?_, ?_⟩
  · intro W hW hUW hWM
    exact deltaStar_strict_overgroup_normalizer hD hW (hDU.trans_le hUW) hWM
  · have he := deltaStar_eq_normalizer_twoCore T hTM hunique hD
    have hC : centralizer (D : Set G) ≤ D := by
      intro x hx
      have hxc : x ∈ centralizer ((normalizer (D : Set G)).pCoreIn 2 : Set G) := by
        change x ∈ centralizer (twoCore (normalizer (D : Set G)) : Set G)
        rw [← he]
        exact hx
      have hc := hD.1.2.1 ⟨centralizer_le_normalizer (D : Set G) hx, hxc⟩
      change x ∈ twoCore (normalizer (D : Set G)) at hc
      rwa [← he] at hc
    exact inf_le_right.trans ((centralizer_le hDU.le).trans (hC.trans hDU.le))

/-- All four conclusions of Lemma 2.3.3(2). -/
theorem deltaStar_sylow_beta (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hD : D ∈ deltaStar (Chapter1.He G) M)
    (S : Sylow 2 ↥(M ⊓ normalizer (D : Set G))) :
    let A := (S : Subgroup ↥(M ⊓ normalizer (D : Set G))).map (M ⊓ normalizer (D : Set G)).subtype
    D < A ∧ Nat.card A < twoPart M ∧ A ∈ beta M ∧
      ∃ R : Sylow 2 (normalizer (D : Set G)),
        (R : Subgroup (normalizer (D : Set G))).map (normalizer (D : Set G)).subtype = A := by
  dsimp only
  let A := (S : Subgroup ↥(M ⊓ normalizer (D : Set G))).map (M ⊓ normalizer (D : Set G)).subtype
  have hDA := deltaStar_sylow_strict T hTM hunique hD S
  have hAM : A ≤ M := (map_subtype_le _).trans inf_le_left
  have hAb := deltaStar_strict_overgroup_beta T hTM hunique hD
    ⟨fun he => hD.1.1.1 (bot_unique (he ▸ hDA.le)), S.isPGroup'.map _⟩ hDA hAM
  obtain ⟨R, hR⟩ := deltaStar_sylow_ambient T hTM hunique hD S
  have hc : Nat.card A = twoPart (normalizer (D : Set G)) :=
    (congrArg (fun W : Subgroup G => Nat.card W) hR).symm.trans (sylow_image_card _ R)
  refine ⟨hDA, ?_, hAb, R, hR⟩
  rw [hc]
  exact twoPart_lt_of_beta_core T hTM hunique hAb ((map_subtype_le _).trans inf_le_right)
    (delta_core_ne hD.1) hD.1.2.2.2


/-- Lemma 2.3.3, both parts. Sylow subgroups are witnessed by their ambient images. -/
theorem lemma_2_3_3 (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hD : D ∈ deltaStar (Chapter1.He G) M)
    (S : Sylow 2 ↥(M ⊓ normalizer (D : Set G))) :
    (∀ U ∈ twoSubgroups, D < U → U ≤ M → U ∈ beta M) ∧
    let A := (S : Subgroup ↥(M ⊓ normalizer (D : Set G))).map (M ⊓ normalizer (D : Set G)).subtype
    D < A ∧ Nat.card A < twoPart M ∧ A ∈ beta M ∧
      ∃ R : Sylow 2 (normalizer (D : Set G)),
        (R : Subgroup (normalizer (D : Set G))).map (normalizer (D : Set G)).subtype = A :=
  ⟨fun _ hU hDU hUM => deltaStar_strict_overgroup_beta T hTM hunique hD hU hDU hUM,
    deltaStar_sylow_beta T hTM hunique hD S⟩

/-- The concrete pair (S,N_G(D)) used after Notation 2.3.4. -/
theorem deltaStar_localPair (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hD : D ∈ deltaStar (Chapter1.He G) M)
    (S : Sylow 2 ↥(M ⊓ normalizer (D : Set G))) :
    ((S : Subgroup ↥(M ⊓ normalizer (D : Set G))).map (M ⊓ normalizer (D : Set G)).subtype,
      normalizer (D : Set G)) ∈ localPairs (Chapter1.He G) M := by
  have hs := deltaStar_sylow_beta T hTM hunique hD S
  exact ⟨hs.2.2.1, hD.1.2.1, delta_core_ne hD.1,
    (map_subtype_le _).trans inf_le_right, hD.1.2.2.2⟩

/-- Nonempty δ supplies a genuine local pair. -/
theorem localPairs_nonempty_of_delta (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) :
    (localPairs (Chapter1.He G) M).Nonempty := by
  obtain ⟨D, hD⟩ := deltaStar_nonempty hdelta
  let S : Sylow 2 ↥(M ⊓ normalizer (D : Set G)) := Classical.choice inferInstance
  exact ⟨_, deltaStar_localPair T hTM hunique hD S⟩

/-- Nonempty δ supplies a local base. -/
theorem localBases_nonempty_of_delta (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) :
    (localBases (Chapter1.He G) M).Nonempty := by
  obtain ⟨P, hP⟩ := localPairs_nonempty_of_delta T hTM hunique hdelta
  exact ⟨P.1, P.2, hP⟩

/-- Nonempty δ supplies a member of Γ. -/
theorem gamma_nonempty_of_delta (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) :
    (gamma (Chapter1.He G) M).Nonempty := by
  obtain ⟨P, hP⟩ := localPairs_nonempty_of_delta T hTM hunique hdelta
  exact ⟨P.2, localPair_snd_mem_gamma hP⟩

/-- Both starred families, and therefore Γ₀, are nonempty. -/
theorem gammaZero_nonempty_of_delta (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) :
    (gammaStar (Chapter1.He G) M).Nonempty ∧
    (gammaMax (Chapter1.He G) M).Nonempty ∧
    (gammaZero (Chapter1.He G) M).Nonempty := by
  have hs := gammaStar_nonempty (localBases_nonempty_of_delta T hTM hunique hdelta)
  have hm := gammaMax_nonempty (gamma_nonempty_of_delta T hTM hunique hdelta)
  obtain ⟨H, hH⟩ := hs
  exact ⟨⟨H, hH⟩, hm, H, Or.inl hH⟩
end CFSG.Quasithin.Chapter2
