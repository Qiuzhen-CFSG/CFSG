module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SevenRatio
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation

/-!
# Component embeddings and prime bounds for the three-centralizer

Starting with precisely the earlier 47.1–47.2 conclusions, embed the selected
A₅ component K into C = C_G(X) and then into its literal quotient C/X.
The latter map is injective because its kernel is central in A₅. Its full
preimage in C is the actual KX, and its index controls the order of C.

Self-centralization of an ambient Sylow five-subgroup rules out 25 dividing
|C|, while K supplies a factor five. Thus every Sylow five of K is Sylow in C.
For the seven exclusion, take the still-unproved local index [N_G(X):C] = 2.
If |C| = 7560, Frattini's argument forces an even ambient seven-normalizer,
so the preliminary ratio 6 or 27 forces its order to be 42. The local
seven-normalizer has order divisible by 21 and dividing 42, contradicting
Sylow's congruence in C. This does not use the assertion printed as 47.4.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, printed p.262.
The two- and three-Sylow bounds and the local index remain explicit inputs
to the last reduction. Perfectness and the A₆ identification are not asserted.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G]

namespace EarlierConclusions
variable {D : Seed G} (E : EarlierConclusions D)
include E

/-- The chosen intrinsic A₅ component centralizes the same selected X. -/
theorem component_le : InvolutionGeometry.rootComponent E.geometry.t ≤ C D := by
  exact le_centralizer_iff.mp E.geometry.X_centralizes_component

/-- The second factor of the actual E₄ × A₅ centralizer model, mapped into G. -/
noncomputable def componentMap : InvolutionGeometry.A5 →* G :=
  E.geometry.model.embedding.comp (MonoidHom.inr _ _)

theorem componentMap_mem (a : InvolutionGeometry.A5) :
    E.componentMap a ∈ InvolutionGeometry.rootComponent E.geometry.t := by
  rw [E.geometry.component_eq]
  exact ⟨(1, a), ⟨rfl, mem_top a⟩, rfl⟩

theorem componentMap_injective : Function.Injective E.componentMap := by
  intro a b h
  exact congrArg Prod.snd (E.geometry.model.embedding_injective h)

/-- The range is the intrinsic ambient component, with the source marking retained. -/
theorem componentMap_range :
    E.componentMap.range = InvolutionGeometry.rootComponent E.geometry.t := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact E.componentMap_mem a
  · rw [E.geometry.component_eq]
    rintro _ ⟨a, ha, rfl⟩
    have ha1 : a.1 = 1 := ha.1
    refine ⟨a.2, ?_⟩
    change E.geometry.model.embedding (1, a.2) = E.geometry.model.embedding a
    congr 1
    exact Prod.ext ha1.symm rfl

/-- The same component embedding with codomain restricted to C_G(X). -/
noncomputable def componentInC : InvolutionGeometry.A5 →* C D :=
  E.componentMap.codRestrict (C D) fun a => E.component_le (E.componentMap_mem a)

theorem componentInC_injective : Function.Injective E.componentInC := by
  intro a b h
  exact E.componentMap_injective (congrArg (fun x : C D => (x : G)) h)

/-- The actual quotient map C → C/X composed with the selected component embedding. -/
noncomputable def quotientComponent : InvolutionGeometry.A5 →* (C D ⧸ XC D) :=
  (QuotientGroup.mk' (XC D)).comp E.componentInC

/-- A central kernel in A₅ is trivial; no A₆ recognition is used. -/
theorem quotientComponent_injective : Function.Injective E.quotientComponent := by
  apply E.quotientComponent.ker_eq_bot_iff.mp
  apply (eq_bot_iff_forall _).mpr
  intro a ha
  have hX : E.componentInC a ∈ XC D := (QuotientGroup.eq_one_iff _).mp ha
  have haZ : a ∈ center InvolutionGeometry.A5 := by
    apply mem_center_iff.mpr
    intro b
    apply E.componentInC_injective
    simpa only [map_mul] using mem_center_iff.mp (XC_le_center D hX) (E.componentInC b)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at haZ
  exact haZ

theorem component_card_dvd : 60 ∣ Nat.card (C D) := by
  have h := card_dvd_of_injective E.componentInC E.componentInC_injective
  simpa only [InvolutionGeometry.card_A5] using h

theorem quotientComponent_card : Nat.card E.quotientComponent.range = 60 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective E.quotientComponent_injective).toEquiv]
  exact InvolutionGeometry.card_A5

/-- The order of C is 3 · 60 times the index of the embedded component in C/X. -/
theorem centralizer_card_eq_component_index :
    Nat.card (C D) = 180 * E.quotientComponent.range.index := by
  have hq := E.quotientComponent.range.index_mul_card
  rw [E.quotientComponent_card] at hq
  have hC := (XC D).index_mul_card
  have hX : Nat.card (XC D) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (X_le_C D)).toEquiv, D.card_X]
  change Nat.card (C D ⧸ XC D) * Nat.card (XC D) = Nat.card (C D) at hC
  rw [hX, ← hq] at hC
  omega

/-- The order calculation gives the degree-six coset action used for recognition. -/
theorem quotientComponent_index_of_card (hC : Nat.card (C D) = 1080) :
    E.quotientComponent.range.index = 6 := by
  have h := E.centralizer_card_eq_component_index
  omega

/-- The literal product KX inside C, expressed as a supremum with central X. -/
noncomputable def componentProduct : Subgroup (C D) := E.componentInC.range ⊔ XC D

/-- The ambient image is precisely the source KX. -/
theorem componentProduct_map :
    E.componentProduct.map (C D).subtype =
      InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X := by
  rw [componentProduct, Subgroup.map_sup,
    map_subgroupOf_eq_of_le (X_le_C D), MonoidHom.map_range]
  change E.componentMap.range ⊔ D.X = _
  rw [E.componentMap_range]

theorem componentProduct_eq_comap : E.componentProduct =
    E.quotientComponent.range.comap (QuotientGroup.mk' (XC D)) := by
  rw [quotientComponent, MonoidHom.range_comp, comap_map_eq, QuotientGroup.ker_mk']
  rfl

theorem componentProduct_index :
    E.componentProduct.index = E.quotientComponent.range.index := by
  rw [E.componentProduct_eq_comap]
  exact E.quotientComponent.range.index_comap_of_surjective
    (QuotientGroup.mk'_surjective _)

/-- The degree of the quotient coset action is the actual relative index [C:KX]. -/
theorem component_relIndex :
    (InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X).relIndex (C D) =
      E.quotientComponent.range.index := by
  rw [← E.componentProduct_map, relIndex, subgroupOf,
    comap_map_eq_self_of_injective (C D).subtype_injective]
  exact E.componentProduct_index

/-- An ambient Sylow five contained in C would force X into that self-centralizing five-group. -/
theorem not_twenty_five_dvd : ¬ 25 ∣ Nat.card (C D) := by
  intro h
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 (C D) := Classical.choice inferInstance
  let A : Subgroup G := (P : Subgroup (C D)).map (C D).subtype
  have hA : IsPGroup 5 A := P.isPGroup'.map (C D).subtype
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  have h25 : 25 ∣ Nat.card A := by
    rw [card_map_of_injective (C D).subtype_injective]
    exact P.pow_dvd_card_of_pow_dvd_card (n := 2) h
  have hAc : Nat.card A = 25 := Nat.dvd_antisymm
    (by simpa only [FiveLocal.sylow_card E.card Q] using card_dvd_of_le hAQ) h25
  have hAe : A = (Q : Subgroup G) := eq_of_le_of_card_ge hAQ
    (by rw [hAc, FiveLocal.sylow_card E.card Q])
  have hQC : (Q : Subgroup G) ≤ C D := hAe ▸ map_subtype_le _
  have hXQ : D.X ≤ (Q : Subgroup G) := by
    rw [← E.five.twoCentral.self_centralizing Q]
    exact le_centralizer_iff.mp hQC
  have h3 := card_dvd_of_le hXQ
  rw [D.card_X, FiveLocal.sylow_card E.card Q] at h3
  norm_num at h3

/-- The exact five-part of the source centralizer. -/
theorem sylow_five_card (P : Sylow 5 (C D)) : Nat.card P = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact P.card_eq_prime_of_dvd_of_not_sq_dvd
    (dvd_trans (by decide : 5 ∣ 60) E.component_card_dvd) E.not_twenty_five_dvd

/-- A Sylow five of the actual component remains Sylow in C_G(X). -/
theorem component_five_isSylow (P : Sylow 5 InvolutionGeometry.A5) :
    ∃ Q : Sylow 5 (C D), (Q : Subgroup (C D)) =
      (P : Subgroup InvolutionGeometry.A5).map E.componentInC := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let S : Sylow 5 (C D) := Classical.choice inferInstance
  have hC : 5 ^ (Nat.card (C D)).factorization 5 = 5 :=
    S.card_eq_multiplicity.symm.trans (E.sylow_five_card S)
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, InvolutionGeometry.card_A5]
    decide +kernel
  have hmap : Nat.card ((P : Subgroup InvolutionGeometry.A5).map E.componentInC) =
      5 ^ (Nat.card (C D)).factorization 5 := by
    rw [card_map_of_injective E.componentInC_injective, hP, hC]
  exact ⟨Sylow.ofCard _ hmap, rfl⟩

/-- The full marked 47.2 contract supplies the two normalizer alternatives. -/
theorem fiveNormalizerTypes : FiveNormalizerTypes G := by
  intro A hA
  rcases E.five.sylow.coverage A hA with h | h
  · obtain ⟨W⟩ := E.five.root A h
    exact Or.inl ⟨W.equiv⟩
  · exact Or.inr (E.five.twoCentral.normalizer A h)

/-- The preliminary source ratio, with all its 47.1–47.2 premises discharged. -/
theorem seven_ratio (P : Sylow 7 G) :
    Nat.card (normalizer (P : Set G)) / 7 = 6 ∨
      Nat.card (normalizer (P : Set G)) / 7 = 27 := by
  exact seven_normalizer_ratio E.card
    (FiveLocal.involution_centralizer_card E.geometry.other E.geometry.model)
    E.fiveNormalizerTypes P

/-- Frattini and Sylow congruences exclude the extra seven factor at index two. -/
theorem centralizer_card_ne_seven_factor (hindex : (CM D).index = 2) :
    Nat.card (C D) ≠ 7560 := by
  intro hC
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let R : Sylow 7 (C D) := Classical.choice inferInstance
  have hR : Nat.card R = 7 := R.card_eq_prime_of_dvd_of_not_sq_dvd
    (by rw [hC]; norm_num) (by rw [hC]; norm_num)
  let A : Subgroup G := (R : Subgroup (C D)).map (C D).subtype
  have hA : Nat.card A = 7 := by
    rw [card_map_of_injective (C D).subtype_injective, hR]
  let Q : Sylow 7 G := Sylow.ofCard A (by rw [hA, E.card]; decide +kernel)
  have hQ : Nat.card Q = 7 := hA
  have hQC : (Q : Subgroup G) ≤ C D := map_subtype_le _
  have hQM := hQC.trans (C_le_M D)
  let QM : Sylow 7 (M D) := Q.subtype hQM
  have hQMC : (QM : Subgroup (M D)) ≤ CM D := fun _ hx => hQC hx
  have hfr := QM.normalizer_sup_eq_top' hQMC
  have hNindex : (CM D).relIndex (normalizer (QM : Set (M D))) = 2 := by
    rw [← relIndex_sup_right, hfr, relIndex_top_right, hindex]
  have hNM : (normalizer (QM : Set (M D))).map (M D).subtype ≤
      normalizer (Q : Set G) := by
    have h := (QM : Subgroup (M D)).le_normalizer_map (M D).subtype
    have he : (QM : Subgroup (M D)).map (M D).subtype = (Q : Subgroup G) := by
      change (Q.subtype hQM : Subgroup (M D)).map _ = _
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hQM]
    rw [he] at h
    exact h
  have hN2 : 2 ∣ Nat.card (normalizer (Q : Set G)) := by
    have hd := card_dvd_of_le hNM
    rw [card_map_of_injective (M D).subtype_injective] at hd
    exact (hNindex ▸ (CM D).relIndex_dvd_card _).trans hd
  have hN7 : 7 ∣ Nat.card (normalizer (Q : Set G)) := by
    simpa only [hQ] using card_dvd_of_le
      (show (Q : Subgroup G) ≤ normalizer (Q : Set G) from le_normalizer)
  have hN : Nat.card (normalizer (Q : Set G)) = 42 := by
    rcases E.seven_ratio Q with h | h <;> omega
  let QC : Sylow 7 (C D) := Q.subtype hQC
  have hNC : (normalizer (QC : Set (C D))).map (C D).subtype ≤
      normalizer (Q : Set G) := by
    have h := (QC : Subgroup (C D)).le_normalizer_map (C D).subtype
    have he : (QC : Subgroup (C D)).map (C D).subtype = (Q : Subgroup G) := by
      change (Q.subtype hQC : Subgroup (C D)).map _ = _
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hQC]
    rw [he] at h
    exact h
  have hdNC : Nat.card (normalizer (QC : Set (C D))) ∣ 42 := by
    have hd := card_dvd_of_le hNC
    rwa [card_map_of_injective (C D).subtype_injective, hN] at hd
  have hXNC : XC D ≤ normalizer (QC : Set (C D)) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro x hx p _
    exact mem_center_iff.mp (XC_le_center D hx) p
  have h3NC : 3 ∣ Nat.card (normalizer (QC : Set (C D))) := by
    have hd := card_dvd_of_le hXNC
    rwa [Nat.card_congr (subgroupOfEquivOfLe (X_le_C D)).toEquiv, D.card_X] at hd
  have hQCcard : Nat.card QC = 7 := by
    change Nat.card (Q.subtype hQC : Subgroup (C D)) = 7
    rw [Sylow.coe_subtype, Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQ]
  have h7NC : 7 ∣ Nat.card (normalizer (QC : Set (C D))) := by
    simpa only [hQCcard] using card_dvd_of_le
      (show (QC : Subgroup (C D)) ≤ normalizer (QC : Set (C D)) from le_normalizer)
  obtain ⟨n, hn⟩ := h7NC
  have hm := QC.card_div_prime_modEq_of_normalizer_card hn
  rw [hC] at hm
  have hb := Nat.le_of_dvd (by decide : 0 < 42) hdNC
  rw [hn] at hb h3NC
  norm_num [Nat.ModEq] at hm
  omega

/-- The remaining Sylow bounds suffice to determine the order after excluding seven. -/
theorem centralizer_card_of_sylow_bounds
    (hindex : (CM D).index = 2)
    (hcard : Nat.card (C D) = 1080 ∨ Nat.card (C D) = 7560) :
    Nat.card (C D) = 1080 :=
  hcard.resolve_right (E.centralizer_card_ne_seven_factor hindex)

end EarlierConclusions
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
