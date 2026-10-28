module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.ComponentRecognition.Intrinsic
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceLocalInputs
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Centralizer
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceAssembly

/-!
# Source application of Lemma 15.4.22

The genuine local data supply the same central four-group, intrinsic Sylow
subgroup and Goldschmidt triple for every factor pair. Applying intrinsic
recognition constructs a normal A₆ supplement and the literal S₆ quotient.
The already proved centralizer equality gives the source denominator C_T(K).
The final application supplies this branch to the 15.4.23 endgame, leaving
only the earlier 15.4.21 normal-factor branch and genuine source inputs.

`Earlier115` records exactly the 1.1.5(2),(3) conclusions and the element
centralizer consequence of 1.1.5(1)/1.1.3(2), for this ambient group. Their
producer is the Chapter 1 source owner; F.6.18 remains with Chapter F.
Source: Aschbacher–Smith 15.4.21–23, printed pp.1164–1165.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open ComponentBranch FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure

namespace CFSG.Quasithin.Chapter15.Section04.SourceRecognition.Source

universe u

open CFSG.Quasithin.Chapter15.Section04.Source
variable {G : Type u} [Group G] [Finite G] {d : Geometry G}

/-- Genuine earlier-source input, restricted to this ambient group.
The first clause is the standard centralizer consequence of 1.1.5(1) and
1.1.3(2), not a later identification. The other two are literal 1.1.5(2),(3).
The existing owner qt-1-01 retains all three and must instantiate this input. -/
def Earlier115 : Prop :=
  ∀ (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G) (hz : z ∈ H),
    Chapter1.Lemma115Hypotheses H S M z →
      HasCharacteristicTwo (centralizer ({(⟨z, hz⟩ : H)} : Set H)) ∧
      (∀ x : pPrimeCore 2 H, (⟨z, hz⟩ : H) * (x : H) * (⟨z, hz⟩ : H)⁻¹ = (x : H)⁻¹) ∧
      (∀ L : Subgroup H, IsComponent H L → HasModelAction115 L z)

omit [Finite G] in
private theorem intrinsic_sylow (h : LocalData d) (i j : Bool) :
    (h.sylow i j : Subgroup (d.I i j)) = d.T₀.subgroupOf (d.I i j) := by
  apply Subgroup.map_injective (d.I i j).subtype_injective
  rw [h.sylow_image, map_subgroupOf_eq_of_le (d.T₀_le_I i j)]

/-- Actual intrinsic triple, retaining both quotient maps and the prescribed Sylow. -/
theorem source_triple (h : LocalData d) (i j : Bool) :
    ChapterF.IsGoldschmidtTriple ((d.G₁ i).subgroupOf (d.I i j))
      ((d.G₂ j).subgroupOf (d.I i j)) := by
  have hA : d.G₁ i ≤ d.I i j := le_sup_left
  have hB : d.G₂ j ≤ d.I i j := le_sup_right
  have heq (U : Subgroup G) (hU : U ≤ d.I i j) :
      ((U.subgroupOf (d.I i j)) ⧸ pCore 2 (U.subgroupOf (d.I i j))) ≃*
        (U ⧸ pCore 2 U) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hU) (pCore_map_iso 2 _)
  refine ⟨?_, ?_, ?_, h.sylow i j, ?_⟩
  · rw [← subgroupOf_sup hA hB, show d.G₁ i ⊔ d.G₂ j = d.I i j from rfl,
      subgroupOf_self]
  · obtain ⟨e⟩ := h.quotient₁ i
    exact ⟨(heq _ hA).trans e⟩
  · obtain ⟨e⟩ := h.quotient₂ j
    exact ⟨(heq _ hB).trans e⟩
  · change ((d.G₁ i ⊓ d.G₂ j).subgroupOf (d.I i j)) = _
    rw [h.intersection, intrinsic_sylow h i j]

private theorem source_odd_core (h : LocalData d)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (source115 : Earlier115 (G := G))
    (i j : Bool) : pPrimeCore 2 (d.I i j) = ⊥ := by
  let I := d.I i j
  let X := (d.X i).subgroupOf I
  let V := (d.V₁ i).subgroupOf I
  let Z := d.Z.subgroupOf I
  have hXI : d.X i ≤ I := d.X_le_I i j
  have hVI : d.V₁ i ≤ I := (h.V₁_le i).trans hXI
  have hZI : d.Z ≤ I := h.Z_le.trans (d.T₀_le_I i j)
  let : IsElementaryAbelian 2 (d.V₁ i) := h.V₁_elementary i
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVI
  have hX : IsPPerfect 2 X := (h.X_perfect i).of_surjective
    (subgroupOfEquivOfLe hXI).symm.toMonoidHom (subgroupOfEquivOfLe hXI).symm.surjective
  have hcomm : ⁅V, X⁆ = V := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVI,
      map_subgroupOf_eq_of_le hXI, h.V₁_full_commutator i]
  have hinter : Z ⊓ (center I ⊔ V) ≠ ⊥ := by
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.central_intersection i j)
    have hmap : (center I ⊔ V).map I.subtype = (center I).map I.subtype ⊔ d.V₁ i := by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hVI]
    have hzmap : (z : G) ∈ (center I ⊔ V).map I.subtype := by
      rw [hmap]
      exact z.property.2
    obtain ⟨x, hx, he⟩ := hzmap
    intro heq
    have hxZ : x ∈ Z := by
      change (x : G) ∈ d.Z
      change (x : G) = (z : G) at he
      rw [he]
      exact z.property.1
    have hx1 := mem_bot.mp (heq ▸ (show x ∈ Z ⊓ (center I ⊔ V) from ⟨hxZ, hx⟩))
    apply hz
    apply Subtype.ext
    exact he.symm.trans (congrArg Subtype.val hx1)
  apply oddCore_eq_bot (h.I_sqtk hG i j).stronglyQuasithin X V Z hX hcomm hinter
  intro z hz
  have hzG : (z : G) ≠ 1 := by
    intro he
    exact hz (Subtype.ext (Subtype.ext he))
  obtain ⟨M, hM⟩ := h.local115 i j (z : G) z.property hzG
  exact (source115 I (h.sylow i j) M (z : G) (z : I).property hM).2.1

/-- Source 15.4.22, with its literal C_T(K) quotient.
The classification inputs remain genuine earlier-source implications. -/
theorem source_lemma_15_4_22 (h : LocalData d)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (source618 : F618Universal.{u} CFSG.KnownSimple.IsKnownSimple)
    (source115 : Earlier115 (G := G)) (i j : Bool)
    (hne : generalizedFitting (d.I i j) ≠ pCore 2 (d.I i j)) :
    ∃ K : Subgroup (d.I i j), K.Normal ∧
      K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤ ∧
      Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
      ∃ hC : (((d.T : Subgroup G) ⊓
        centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j)).Normal,
        let _ := hC
        Nonempty (((d.I i j) ⧸ (((d.T : Subgroup G) ⊓
          centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j))) ≃*
            Equiv.Perm (Fin 6)) := by
  classical
  let I := d.I i j
  let A := (d.G₁ i).subgroupOf I
  let B := (d.G₂ j).subgroupOf I
  let Z := d.Z.subgroupOf I
  let S := h.sylow i j
  have hZI : d.Z ≤ I := h.Z_le.trans (d.T₀_le_I i j)
  let : IsElementaryAbelian 2 d.Z := h.Z_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf hZI
  have hcard : Nat.card Z = 4 := (Nat.card_congr (subgroupOfEquivOfLe hZI).toEquiv).trans h.Z_card
  have hZS : Z ≤ (S : Subgroup I) := by
    rw [intrinsic_sylow h i j]
    exact subgroupOf_mono I h.Z_le
  have hS : A ⊓ B = (S : Subgroup I) := by
    change ((d.G₁ i ⊓ d.G₂ j).subgroupOf I) = _
    rw [h.intersection, intrinsic_sylow h i j]
  have hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I) := by
    intro s hs z hz
    apply Subtype.ext
    have hsT : (s : G) ∈ (d.T : Subgroup G) := by
      apply d.T₀_le_T
      rw [← h.sylow_image i j]
      exact mem_map_of_mem I.subtype hs
    exact (h.centralizer_Z ▸ hsT) (z : G) hz
  have hZQ : Z ⊓ pCore 2 I = ⊥ := by
    have hamb : d.Z ⊓ I.pCoreIn 2 = ⊥ := by
      by_contra hb
      exact hne (h.fitting_of_Z_meets_core i j hb)
    apply le_bot_iff.mp
    intro z hz
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hamb ▸ (show (z : G) ∈ d.Z ⊓ I.pCoreIn 2 from
      ⟨hz.1, mem_map_of_mem I.subtype hz.2⟩))
  have h115 (z : Z) (hz : z ≠ 1) :
      HasCharacteristicTwo (centralizer ({(z : I)} : Set I)) ∧
      (∀ x : pPrimeCore 2 I, (z : I) * (x : I) * (z : I)⁻¹ = (x : I)⁻¹) ∧
      (∀ L : Subgroup I, IsComponent I L → HasModelAction115 L (z : G)) := by
    have hzG : (z : G) ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext he))
    obtain ⟨M, hM⟩ := h.local115 i j (z : G) z.property hzG
    exact source115 I S M (z : G) (z : I).property hM
  have hc : ∀ z : Z, z ≠ 1 → HasCharacteristicTwo (centralizer ({(z : I)} : Set I)) :=
    fun z hz => (h115 z hz).1
  have hm : ∀ L : Subgroup I, IsComponent I L → ∀ z : Z, z ≠ 1 →
      ∃ α : MulAut L, (∀ x : L, (α x : I) = (z : I) * (x : I) * (z : I)⁻¹) ∧
        ModelAction115 L α := by
    intro L hL z hz
    obtain ⟨α, heval, hmodel⟩ := (h115 z hz).2.2 L hL
    exact ⟨α, fun x => Subtype.ext (heval x), hmodel⟩
  obtain ⟨K, hKn, hgen, ⟨eK⟩, hquot, ⟨eC⟩⟩ := intrinsic_recognition source618
    (h.I_sqtk hG i j) A B (source_triple h i j) S hS Z hZS hSZ hcard hZQ
    (source_odd_core h hG source115 i j) hne hc hm
  let : K.Normal := hKn
  have hKZ : center K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := (Subgroup.centerCongr eK ⟨x, hx⟩).property
    change eK x ∈ center (alternatingGroup (Fin 6)) at he
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact mem_bot.mpr (eK.injective (he.trans eK.map_one.symm))
  have hfactor (U : Subgroup G) (hUI : U ≤ I) (hU : IsPPerfect 2 U) :
      U ≤ K.map I.subtype := by
    have hp : IsPPerfect 2 (U.subgroupOf I) := hU.of_surjective
      (subgroupOfEquivOfLe hUI).symm.toMonoidHom (subgroupOfEquivOfLe hUI).symm.surjective
    have hUK : U.subgroupOf I ≤ K :=
      (le_pResidual_of_isPPerfect _ hp).trans (sInf_le ⟨hKn, hquot⟩)
    simpa only [map_subgroupOf_eq_of_le hUI] using map_mono (f := I.subtype) hUK
  have heq := h.centralizer_T_subgroupOf_eq i j K hgen hKZ
    (hfactor _ (d.X_le_I i j) (h.X_perfect i))
    (hfactor _ (d.Y_le_I i j) (h.Y_perfect j))
  have hC : (((d.T : Subgroup G) ⊓ centralizer (K.map I.subtype : Set G)).subgroupOf I).Normal := by
    rw [heq]
    infer_instance
  refine ⟨K, hKn, hgen, ⟨eK⟩, hC, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans eC⟩


/-- Supply the proved component branch to the actual source endgame. The
remaining normal-factor premise is the earlier Lemma 15.4.21. -/
theorem false_of_source_twoCore_branch (h : LocalData d)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (source618 : F618Universal.{u} CFSG.KnownSimple.IsKnownSimple)
    (source115 : Earlier115 (G := G))
    (h21 : ∀ i j, generalizedFitting (d.I i j) = pCore 2 (d.I i j) →
      ((d.X i).subgroupOf (d.I i j)).Normal) : False :=
  h.false_of_source_local_alternatives h21
    (source_lemma_15_4_22 h hG source618 source115)

end CFSG.Quasithin.Chapter15.Section04.SourceRecognition.Source
