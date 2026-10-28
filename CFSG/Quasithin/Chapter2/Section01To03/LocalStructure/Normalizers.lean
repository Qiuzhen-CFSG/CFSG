module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Centers
public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Characteristic normalizers in Γ₀

Source: Aschbacher–Smith, proof of 2.3.8(4–5), printed p.524.
If the chosen Sylow S itself occurs as a local base in a new member K of Γ,
2.3.6 makes it a largest base, so both starred maximalities transport S to K.
If K also contains N_G(S), the p-group normalizer condition would make S
Sylow in G, contradicting uniqueness of M. Apply this to characteristic
subgroups of S, using characteristic-two inheritance for their relative
normalizers in H.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H U L K : Subgroup G}

/-- A local pair based on the full Sylow supplies the extra largest-base
condition needed for the superscript-star family. -/
theorem gammaZero_sylow_transport_of_full_base
    (hH : H ∈ gammaZero (Chapter1.He G) M) (S : Sylow 2 H)
    (hK : K ∈ gamma (Chapter1.He G) M)
    (hbase : ∃ L, ((S : Subgroup H).map H.subtype, L) ∈
      localPairsIn (Chapter1.He G) M K) :
    K ∈ gammaZero (Chapter1.He G) M ∧
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = (S : Subgroup H).map H.subtype := by
  obtain ⟨L, hL⟩ := hbase
  have hSK := hL.1.2.2.2.1.trans hL.2
  have hc : twoPart H ≤ twoPart K := by
    rw [← sylow_image_card H S]
    exact beta_card_le_twoPart hL.1.1 hSK
  have hbig : K ∈ gammaWithLargestBase (Chapter1.He G) M := by
    refine ⟨hK, ((S : Subgroup H).map H.subtype, L), hL, ?_⟩
    intro V hV
    rw [sylow_image_card]
    exact gammaZero_card_bound hH hV
  have hresult : K ∈ gammaZero (Chapter1.He G) M ∧ twoPart K = twoPart H := by
    rcases hH with hs | hm
    · have hr := gammaStar_of_twoPart_le hs hbig hc
      exact ⟨Or.inl hr.1, hr.2⟩
    · have hr := gammaMax_of_twoPart_le hm hK hc
      exact ⟨Or.inr hr.1, hr.2⟩
  exact ⟨hresult.1, (gamma_sylow_transport hK S hSK hresult.2 hL.1.1.2.1).1⟩

/-- The normalizer condition rules out a Γ overgroup containing N_G(S)
once S is itself a local base in that overgroup. -/
theorem gammaZero_full_base_normalizer_not_le (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M) (S : Sylow 2 H)
    (hK : K ∈ gamma (Chapter1.He G) M)
    (hbase : ∃ L, ((S : Subgroup H).map H.subtype, L) ∈
      localPairsIn (Chapter1.He G) M K) :
    ¬ normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ K := by
  intro hNK
  let A := (S : Subgroup H).map H.subtype
  obtain ⟨P, hP⟩ := (gammaZero_sylow_transport_of_full_base hH S hK hbase).2
  change (P : Subgroup K).map K.subtype = A at hP
  obtain ⟨R, hAR⟩ := (S.isPGroup'.map H.subtype).exists_le_sylow
  have hinf : (R : Subgroup G) ⊓ K = A := by
    rw [← hP]
    exact inf_eq_sylow_map P R.isPGroup' (hP.symm ▸ hAR)
  let : Group.IsNilpotent (R : Subgroup G) := R.isPGroup'.isNilpotent
  have hself : normalizer (A.subgroupOf (R : Subgroup G) : Set (R : Subgroup G)) =
      A.subgroupOf (R : Subgroup G) := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hAR]
    intro x hx
    exact (show (x : G) ∈ A from hinf ▸ ⟨x.property, hNK hx⟩)
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (R : Subgroup G))) _ hself
  have he : (R : Subgroup G) = A := le_antisymm (subgroupOf_eq_top.mp htop) hAR
  obtain ⟨L, hL⟩ := hbase
  have hRM : (R : Subgroup G) ≤ M := he ▸ hL.1.1.2.1
  apply gamma_not_le hK
  apply core_overgroup_le_of_sylow T hTM hunique hK.1 (R.subtype hRM)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM, he, ← hP]
  exact map_subtype_le _

/-- Relative normalizers of nontrivial characteristic subgroups of S lie
in M. The normalizer containment is an equivalent usable invariance input. -/
theorem gammaZero_relative_normalizer_le (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M) (he : H ∈ Chapter1.He G)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {R : Subgroup G} (hR : R ≠ ⊥) (hRS : R ≤ (S : Subgroup H).map H.subtype)
    (hchar : normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ normalizer (R : Set G)) :
    H ⊓ normalizer (R : Set G) ≤ M := by
  by_contra hout
  let A := (S : Subgroup H).map H.subtype
  let N := normalizer (R : Set G)
  let D := H ⊓ N
  have hp := (S.isPGroup'.map H.subtype).to_le hRS
  have hAD : A ≤ D := le_inf (map_subtype_le _) (A.le_normalizer.trans hchar)
  have hcore : R ≤ twoCore D := le_pCoreIn_of_normalizes hp
    (hRS.trans hAD) inf_le_right
  have hpairA : (A, D) ∈ localPairs (Chapter1.He G) M :=
    ⟨beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype),
      Chapter1.normalizer_mem_He_of_isPGroup he hp (hRS.trans (map_subtype_le _)),
      fun heq => hR (bot_unique (heq ▸ hcore)), hAD, hout⟩
  have hN : N ∈ gamma (Chapter1.He G) M := by
    refine ⟨?_, (A, D), hpairA, inf_le_right⟩
    intro hn
    exact hR (bot_unique (hn ▸ le_pCoreIn_of_normalizes hp R.le_normalizer le_rfl))
  exact gammaZero_full_base_normalizer_not_le T hTM hunique hH S hN
    ⟨D, hpairA, inf_le_right⟩ hchar

end CFSG.Quasithin.Chapter2
