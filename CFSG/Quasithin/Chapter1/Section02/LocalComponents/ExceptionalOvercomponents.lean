module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ContainingModels
/-!
# Exceptional local overcomponents: J₂ and the M₂₃ reduction

Work inside the literal join K ∨ T. Unique containing C-components identify
its intrinsic K with the component supplied by the checked earlier-source
inspection. J₂ admits no enlargement, while the M₂₃ inspection leaves only
M₂₃ or J₄. The latter alternative is retained explicitly, not excluded here.
All equivalences preserve the intrinsic quotients by O₂.

Source: Aschbacher–Smith A.3.12, pp.47–48, and 1.2.8, pp.506–507.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
open ChapterA.Section03.SourceEmbeddings

/-- A normalized local J₂ section admits no proper local overcomponent. -/
theorem eq_of_jankoTwo_local_overcomponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.LeechRelated.J2.Carrier)) : X = K := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH, hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  have hq := uniqueness_local_quotient_sqtk hG hK.2.2
  have hm : Nonempty (((X.subgroupOf H) ⧸ pCore 2 (X.subgroupOf H)) ≃*
      Sporadic.LeechRelated.J2.Carrier) :=
    ⟨(QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))).trans h.some⟩
  have hc := (Exceptional.jankoTwo_local_isCComponent_normal hq S hx hn' hm).1
  have he := hc.eq_of_le hK.1 (comap_mono hXK)
  change X.subgroupOf H = K.subgroupOf H at he
  have hh := congrArg (map H.subtype) he
  have hxmap : (X.subgroupOf H).map H.subtype = X := map_subgroupOf_eq_of_le hXH
  have hkmap : (K.subgroupOf H).map H.subtype = K := map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)
  rw [hxmap, hkmap] at hh
  exact hh

end CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
open ChapterA.Section03.SourceEmbeddings

/-- In particular, the normalized J₂ seed itself is maximal in the local family. -/
theorem jankoTwo_mem_LStar
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    X ∈ LStar G (T : Subgroup G) :=
  ⟨hX, fun _ hK hXK => (eq_of_jankoTwo_local_overcomponent hG T hX hn hK hXK h).symm⟩
end CFSG.Quasithin.Chapter1.Section02


noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
open ChapterA.Section03.SourceEmbeddings

/-- Lift the checked exceptional containing catalogue to the original two-core quotient. -/
theorem exceptional_local_overcomponent_models_or_jankoFour
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Exceptional.IsModel (X ⧸ pCore 2 X)) :
    X = K ∨ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH, hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  have hq := uniqueness_local_quotient_sqtk hG hK.2.2
  have hm : Exceptional.IsModel ((X.subgroupOf H) ⧸ pCore 2 (X.subgroupOf H)) :=
    h.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hXH)))
  obtain ⟨C,hC,_,hXC,hmodels⟩ := Exceptional.exists_normal_containing_models hq S hx hn' hm
  obtain ⟨D, _, hu⟩ := lemma_1_2_4_containment_of_A_3_12
    (containment_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hq S hx
  have he : C = K.subgroupOf H :=
    (hu _ ⟨hC,hXC⟩).trans (hu _ ⟨hK.1,comap_mono hXK⟩).symm
  rw [he] at hmodels
  let eK := QuotientGroup.congr _ _
    (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  rcases hmodels with he | hJ | hM | hJ4
  · left
    simpa only [map_subgroupOf_eq_of_le hXH,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] using
      congrArg (map H.subtype) he
  · exact Or.inr (Or.inl ⟨eK.symm.trans hJ.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eK.symm.trans hM.some⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨eK.symm.trans hJ4.some⟩))
end CFSG.Quasithin.Chapter1.Section02

noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem coreQuotient_card_dvd {X K : Subgroup G} (hXK : X ≤ K) :
    Nat.card (X ⧸ pCore 2 X) ∣ Nat.card (K ⧸ pCore 2 K) := by
  let B := X.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXK)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXK))
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap B) (q.subgroupMap_surjective B) hk
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr a.toEquiv]
  exact (card_quotient_dvd_card _).trans (B.map q).card_subgroup_dvd_card
end CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Only the J₄ containing row is left by the checked M₂₃ inspection. -/
theorem mathieuTwentyThree_local_overcomponent_or_jankoFour
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  rcases exceptional_local_overcomponent_models_or_jankoFour hG T hX hn hK hXK
    (Or.inr (Or.inl h)) with he | hJ | hM | hJ4
  · exact Or.inl (he ▸ h)
  · have hd := coreQuotient_card_dvd hXK
    rw [Nat.card_congr h.some.toEquiv, Sporadic.Mathieu.m23_order,
      Nat.card_congr hJ.some.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
    norm_num at hd
  · exact Or.inl hM
  · exact Or.inr hJ4
end CFSG.Quasithin.Chapter1.Section02
