module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.Placement
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Sylow supplements and the four factor intersections

The Sylow witness for `XS` in 15.4.12 places each factor's two-core in `S`:
the core and `S` generate a two-group, so Sylow maximality bounds the core.
A factor whose core quotient has order three therefore has index three over
any normalizing two-supplement containing `S`. The coprime-index criterion
constructs the actual Sylow subgroup with that supplement as its ambient image.
The outside-factor statement of 15.4.19 then forces `G₁ ∩ G₂ = T₀` for every
pair of factors, without an extra index-three premise.

Normality is relative to the displayed overgroup, and every intrinsic core
and Sylow subgroup is mapped through the subgroup inclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1160 and 1163–1164, 15.4.12(4,6) and the notation around 15.4.20.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A core normalized by the Sylow supplement lies in that Sylow subgroup. -/
theorem factor_core_le_sylow_supplement {L S : Subgroup G}
    (hn : S ≤ normalizer (L : Set G))
    (P : Sylow 2 (L ⊔ S : Subgroup G))
    (hP : (P : Subgroup (L ⊔ S : Subgroup G)).map (L ⊔ S : Subgroup G).subtype = S) :
    L.pCoreIn 2 ≤ S := by
  have hnC : L ⊔ S ≤ normalizer (L.pCoreIn 2 : Set G) :=
    (sup_le L.le_normalizer hn).trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
    ((pCoreIn_le 2 L).trans le_sup_left) hnC).trans ((pCoreIn_le_sylow _ P).trans_eq hP)

/-- A factor with core quotient of order three has index three over every
normalizing two-supplement containing its core. This supplies the previously
separate index hypothesis for the four intersections in 15.4.20. -/
theorem factor_index_three_of_core_quotient {L U : Subgroup G}
    (hU : IsPGroup 2 U) (hn : U ≤ normalizer (L : Set G))
    (hcore : L.pCoreIn 2 ≤ U) (hq : Nat.card (L ⧸ pCore 2 L) = 3) :
    U.relIndex (L ⊔ U) = 3 ∧
    ∃ P : Sylow 2 (L ⊔ U : Subgroup G),
      (P : Subgroup (L ⊔ U : Subgroup G)).map (L ⊔ U : Subgroup G).subtype = U := by
  have hcindex : (pCore 2 L).index = 3 := hq
  have hodd : ¬ 2 ∣ (pCore 2 L).index := by rw [hcindex]; decide
  let Q : Sylow 2 L := (pCore_isPGroup (p := 2) (G := L)).toSylow hodd
  have hcoreU : (pCore 2 L) ≤ U.subgroupOf L := by
    intro x hx
    exact hcore ⟨x, hx, rfl⟩
  have hsub : U.subgroupOf L = pCore 2 L :=
    Q.is_maximal' (hU.comap_of_injective L.subtype L.subtype_injective) hcoreU
  have hinf : L ⊓ U = L.pCoreIn 2 := by
    rw [pCoreIn, ← hsub, subgroupOf_map_subtype]
    exact inf_comm _ _
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes L U hn
  rw [hinf] at hprod
  have hLc : Nat.card L = Nat.card (L.pCoreIn 2) * 3 := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup L) (pCore 2 L) ⊤ bot_le le_top
    rw [relIndex_bot_left, relIndex_top_right, hcindex, relIndex_bot_left, card_top] at h
    simpa only [pCoreIn, card_map_of_injective L.subtype_injective] using h.symm
  rw [hLc] at hprod
  have hcard : Nat.card (L ⊔ U : Subgroup G) = Nat.card U * 3 := by
    have hc : 0 < Nat.card (L.pCoreIn 2) := Nat.card_pos
    nlinarith
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) U (L ⊔ U) bot_le le_sup_right
  rw [relIndex_bot_left, relIndex_bot_left, hcard] at hi
  have hindex : U.relIndex (L ⊔ U) = 3 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  exact ⟨hindex, IsPGroup.exists_sylow_sup_of_coprime_index L U hU hn (pCore 2 L) hodd hcore⟩



omit [Finite G] in
/-- A two-subgroup normalized by an intrinsic Sylow subgroup lies in its image. -/
theorem two_subgroup_le_sylow_image_of_normalized {H A S : Subgroup G}
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = S)
    (hA : IsPGroup 2 A) (hAH : A ≤ H) (hn : S ≤ normalizer (A : Set G)) : A ≤ S := by
  have hSH : S ≤ H := hP ▸ map_subtype_le _
  have hSp : IsPGroup 2 S := hP ▸ P.isPGroup'.map H.subtype
  have hASp : IsPGroup 2 (A ⊔ S : Subgroup G) := hA.to_sup_of_normal_left' hSp hn
  have hAS : A ⊔ S ≤ H := sup_le hAH hSH
  have hPS : (P : Subgroup H) ≤ (A ⊔ S).subgroupOf H := by
    intro p hp
    exact mem_sup_right (hP ▸ (show (p : G) ∈ (P : Subgroup H).map H.subtype from ⟨p, hp, rfl⟩))
  have heq := P.is_maximal' (hASp.comap_of_injective H.subtype H.subtype_injective) hPS
  intro a ha
  have hmem : (⟨a, hAH ha⟩ : H) ∈ (P : Subgroup H) := heq ▸ (show
    (⟨a, hAH ha⟩ : H) ∈ (A ⊔ S).subgroupOf H from mem_sup_left ha)
  exact hP ▸ (show a ∈ (P : Subgroup H).map H.subtype from ⟨⟨a, hAH ha⟩, hmem, rfl⟩)

/-- The source Sylow witness for the whole product restricts to either factor,
then extends to every normalizing two-supplement. -/
theorem factor_indices_from_whole_sylow (L : Bool → Subgroup G) {S U : Subgroup G}
    (hSU : S ≤ U) (hU : IsPGroup 2 U)
    (hn : ∀ i, U ≤ normalizer (L i : Set G))
    (hq : ∀ i, Nat.card (L i ⧸ pCore 2 (L i)) = 3)
    (P : Sylow 2 ((L false ⊔ L true) ⊔ S : Subgroup G))
    (hP : (P : Subgroup ((L false ⊔ L true) ⊔ S : Subgroup G)).map
      ((L false ⊔ L true) ⊔ S : Subgroup G).subtype = S) :
    ∀ i, U.relIndex (L i ⊔ U) = 3 ∧
      ∃ Q : Sylow 2 (L i ⊔ U : Subgroup G),
        (Q : Subgroup (L i ⊔ U : Subgroup G)).map (L i ⊔ U : Subgroup G).subtype = U := by
  intro i
  have hL : L i ≤ L false ⊔ L true := by
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hcH : (L i).pCoreIn 2 ≤ (L false ⊔ L true) ⊔ S :=
    ((pCoreIn_le 2 (L i)).trans hL).trans le_sup_left
  have hncore : S ≤ normalizer ((L i).pCoreIn 2 : Set G) :=
    (hSU.trans (hn i)).trans (normalizer_le_normalizer_characteristic_image (L i) (pCore 2 (L i)))
  have hcore : (L i).pCoreIn 2 ≤ U :=
    (two_subgroup_le_sylow_image_of_normalized P hP (isPGroup_pCoreIn 2 (L i)) hcH hncore).trans hSU
  exact factor_index_three_of_core_quotient hU (hn i) hcore (hq i)

/-- The actual common subgroup in all four triples, with the index-three
premise discharged from the 15.4.12 quotient and Sylow inputs. -/
theorem factor_intersections_from_source_quotients (d : Source.Geometry G)
    (hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀)
    (hnX : ∀ i, d.T₀ ≤ normalizer (d.X i : Set G))
    (hqX : ∀ i, Nat.card (d.X i ⧸ pCore 2 (d.X i)) = 3)
    (P : Sylow 2 (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G))
    (hP : (P : Subgroup (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G)).map
      (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G).subtype =
        ChapterB.baumann (d.T : Subgroup G))
    (hT₂ : (d.T : Subgroup G) ≤ d.M₂) (houtside : ∀ i, ¬ d.X i ≤ d.M₂) :
    (∀ i, d.T₀.relIndex (d.G₁ i) = 3) ∧
    (∀ i, ∃ Q : Sylow 2 (d.G₁ i), (Q : Subgroup (d.G₁ i)).map (d.G₁ i).subtype = d.T₀) ∧
    (∀ i j, d.G₁ i ⊓ d.G₂ j = d.T₀) := by
  have h := factor_indices_from_whole_sylow d.X hS (d.T.isPGroup'.to_le d.T₀_le_T) hnX hqX P hP
  exact ⟨fun i => (h i).1, fun i => (h i).2,
    factor_intersections_eq_T₀ d hT₂ houtside (fun i => (h i).1)⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
