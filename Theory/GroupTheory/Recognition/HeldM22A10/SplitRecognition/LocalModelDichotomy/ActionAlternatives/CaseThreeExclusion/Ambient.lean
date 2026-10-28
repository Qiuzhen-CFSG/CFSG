module

public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# The ambient transfer contradiction for Janko Case III

A common centralizer of order sixteen whose derived subgroup is the original
involution line is Sylow in the second involution centralizer. Indeed its
normalizer fixes the characteristic derived line, and the normalizer condition
then forces maximality. Transfer into an index-two subgroup contradicts the
existence of an elementary group of order sixteen centralizing every involution
there. The local matrix computations are explicit premises of this module.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, p.3, DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion
open Subgroup
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)

/-- The characteristic derived involution line makes the common centralizer
Sylow in the full ambient centralizer of the other element. -/
public theorem commonCentralizer_sylow (d : G)
    (hcard : Nat.card (D.centralizer ⊓ centralizer ({d} : Set G) : Subgroup G) = 16)
    (hderived : ⁅D.centralizer ⊓ centralizer ({d} : Set G),
      D.centralizer ⊓ centralizer ({d} : Set G)⁆ = zpowers D.z) :
    ∃ S : Sylow 2 (centralizer ({d} : Set G)),
      (S : Subgroup _) =
        (D.centralizer ⊓ centralizer ({d} : Set G)).subgroupOf
          (centralizer ({d} : Set G)) := by
  let L := D.centralizer ⊓ centralizer ({d} : Set G)
  have hp : IsPGroup 2 L := IsPGroup.of_card (n := 4) hcard
  have hn : normalizer (L : Set G) ≤ D.centralizer :=
    normalizer_le_centralizer_of_characteristic_involution L (_root_.commutator L)
      D.z D.z_order ((map_subtype_commutator L).trans hderived)
  apply exists_sylow_eq_of_isPGroup_of_normalizer_eq _ hp.comap_subtype
  apply le_antisymm _ le_normalizer
  change normalizer (L.subgroupOf (centralizer ({d} : Set G)) : Set _) ≤
    L.subgroupOf (centralizer ({d} : Set G))
  rw [← subgroupOf_normalizer_eq (show L ≤ centralizer ({d} : Set G) from inf_le_right)]
  intro x hx
  exact ⟨hn hx, x.property⟩

private theorem no_normal_index_two [IsSimpleGroup G]
    (D : LocalData G) (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · rw [index_bot]
    have hle : 384 ≤ Nat.card G := by
      rw [← D.centralizer_card]
      exact Nat.card_le_card_of_injective _ D.centralizer.subtype_injective
    omega
  · simp

omit [Finite G] in
private theorem not_commutative_of_derived_line
    (L : Subgroup G) (hderived : ⁅L, L⁆ = zpowers D.z) : ¬ IsMulCommutative L := by
  intro hc
  let := hc
  have he : (⊥ : Subgroup G) = zpowers D.z := by
    rw [← hderived, ← map_subtype_commutator, commutator_eq_bot, Subgroup.map_bot]
  have hz : D.z ∈ (⊥ : Subgroup G) := he.symm ▸ mem_zpowers D.z
  exact D.z_ne_one hz

/-- Transfer and characteristic-line normalizer control exclude the precise
local configuration used by Janko. The displayed local hypotheses remain to
be verified in the Case III coordinates. -/
public theorem false_of_local_configuration [IsSimpleGroup G]
    (T H : Subgroup G) (d : G)
    (hT : Nat.card T = 128) (hHT : H ≤ T) (hH : Nat.card H = 64)
    (hdT : d ∈ T) (hd : orderOf d = 2)
    (hcard : Nat.card (D.centralizer ⊓ centralizer ({d} : Set G) : Subgroup G) = 16)
    (hderived : ⁅D.centralizer ⊓ centralizer ({d} : Set G),
      D.centralizer ⊓ centralizer ({d} : Set G)⁆ = zpowers D.z)
    (helementary : ∀ t : G, t ∈ H → orderOf t = 2 →
      ∃ E : Subgroup G, E ≤ centralizer ({t} : Set G) ∧
        IsElementaryAbelian 2 E ∧ Nat.card E = 16) : False := by
  let S : Sylow 2 G := Sylow.ofCard T (by
    rw [← D.sylow.card_eq_multiplicity, hT, D.sylow_card])
  have hindex : (H.subgroupOf (S : Subgroup G)).index = 2 := by
    have hHcard : Nat.card (H.subgroupOf (S : Subgroup G)) = 64 :=
      (Nat.card_congr (subgroupOfEquivOfLe hHT).toEquiv).trans hH
    have he := (H.subgroupOf (S : Subgroup G)).card_mul_index
    change _ = Nat.card T at he
    rw [hHcard, hT] at he
    omega
  obtain ⟨t, hconj, htH⟩ := S.exists_isConj_mem_of_index_two (no_normal_index_two D)
    (H.subgroupOf (S : Subgroup G)) hindex ⟨d, hdT⟩
    (by
      change orderOf (⟨d, hdT⟩ : (S : Subgroup G)) = 2
      exact (Subgroup.orderOf_coe _).symm.trans hd)
  have hdconj : IsConj d (t : G) := hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hdconj
  let f : G ≃* G := MulAut.conj g
  have hfd : f d = t := hg
  have htorder : orderOf (t : G) = 2 := by
    rw [← hfd]
    exact (orderOf_injective f.toMonoidHom f.injective d).trans hd
  obtain ⟨E, hEt, hEelem, hEcard⟩ := helementary t htH htorder
  let := hEelem
  let A := E.map f.symm.toMonoidHom
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAcard : Nat.card A = 16 := by
    rw [card_map_of_injective f.symm.injective, hEcard]
  have hAd : A ≤ centralizer ({d} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply f.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, f.apply_symm_apply, hfd] using
      mem_centralizer_singleton_iff.mp (hEt hy)
  let C := centralizer ({d} : Set G)
  let L := D.centralizer ⊓ C
  let F := A.subgroupOf C
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hAd
  have hFcard : Nat.card F = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAd).toEquiv).trans hAcard
  obtain ⟨P, hP⟩ := commonCentralizer_sylow D d hcard hderived
  let eLP : L ≃* P := (subgroupOfEquivOfLe (show L ≤ C from inf_le_right)).symm.trans
    (MulEquiv.subgroupCongr hP.symm)
  have hPcard : Nat.card P = 16 :=
    (Nat.card_congr eLP.symm.toEquiv).trans hcard
  obtain ⟨Q, hFQ⟩ := (IsElementaryAbelian.isPGroup 2 F).exists_le_sylow
  have hQcard : Nat.card Q = 16 :=
    (Nat.card_congr (Q.equiv P).toEquiv).trans hPcard
  have hFQeq : F = (Q : Subgroup C) := eq_of_le_of_card_ge hFQ (by omega)
  let e : L ≃* F := eLP.trans ((P.equiv Q).trans (MulEquiv.subgroupCongr hFQeq.symm))
  apply not_commutative_of_derived_line D L hderived
  exact ⟨⟨fun x y => e.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion
