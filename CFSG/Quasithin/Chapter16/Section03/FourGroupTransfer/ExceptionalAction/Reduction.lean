module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ComponentRestriction
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Reduction

/-!
# Conjugation and the nontrivial core in 16.3.5

The subgroup of order four may be cyclic. Cauchy's theorem supplies the
involution used in 16.1.7, and ambient conjugation acts on its literal layer
closure. To apply 16.3.4, first conjugate the other involution into the fixed
T_C inside C_G(L). Transporting the relative component and commutator data
then constructs the required ExclusionSetup with the involutions exchanged.
Only after this construction can the full-group exclusion prove O₂(I) ≠ 1.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.4–5, printed pp.1178–1179 / PDF pp.1195–1196.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
open Subgroup Theory.GroupTheory ClassificationModels
variable {G : Type*} [Group G]

private theorem layer_normal (H : Type*) [Group H] : (componentLayer H).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [le_normalizer_iff]
  intro g _ x hx
  have hm : (componentLayer H).map (MulAut.conj g).toMonoidHom ≤ componentLayer H := by
    rw [componentLayer, sSup_eq_iSup', Subgroup.map_iSup]
    apply iSup_le
    intro J
    exact le_iSup_of_le ⟨_, J.property.map_conj g⟩ le_rfl
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

private theorem normalizes_layerIn (H : Subgroup G) :
    H ≤ normalizer (ComponentTransfer.layerIn H) := by
  let := layer_normal H
  have hn := (componentLayer H).le_normalizer_map H.subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
  exact hn

private theorem normalizes_orbit (A L B : Subgroup G)
    (hL : A ≤ normalizer L) (hB : A ≤ normalizer B) :
    A ≤ normalizer (componentOrbit L B) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have hm : (componentOrbit L B).map (MulAut.conj a).toMonoidHom ≤ componentOrbit L B := by
    change (⨆ b : B, L.map (MulAut.conj (b : G)).toMonoidHom).map _ ≤ _
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro b
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    have hb : a * (b : G) * a⁻¹ ∈ B := (mem_normalizer_iff.mp (hB ha) b).mp b.property
    have hl' : a * l * a⁻¹ ∈ L := (mem_normalizer_iff.mp (hL ha) l).mp hl
    apply (le_iSup (fun b : B => L.map (MulAut.conj (b : G)).toMonoidHom)
      ⟨a * b * a⁻¹, hb⟩)
    refine ⟨a * l * a⁻¹, hl', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)

/-- The action on the literal layer closure is supplied by ambient conjugation. -/
theorem normalizes_enlargement {E L : Subgroup G} {i : G}
    (hEL : E ≤ centralizer (L : Set G))
    (hi : i ∈ centralizer ((E ⊔ L : Subgroup G) : Set G)) :
    E ≤ normalizer (ComponentTransfer.layerClosure (involutionCentralizer i) L) := by
  apply normalizes_orbit E L (ComponentTransfer.layerIn (involutionCentralizer i))
    (hEL.trans (centralizer_le_normalizer _))
  apply le_trans _ (normalizes_layerIn _)
  intro e he
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hi e ((le_sup_left : E ≤ E ⊔ L) he))

/-- Cauchy's theorem supplies an involution even when E is cyclic of order four. -/
theorem exists_involution (E : Subgroup G) (hcard : Nat.card E = 4) :
    ∃ t : G, t ∈ E ∧ orderOf t = 2 := by
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; decide : 2 ∣ Nat.card E)
  exact ⟨t, t.property, (orderOf_coe t).trans ht⟩

/-- The input for 16.1.7, constructed for an arbitrary involution in E. -/
theorem transfer_setup {E L : Subgroup G} {i t : G}
    (hc : CentralizesAsComponent E L) (htE : t ∈ E) (ht : orderOf t = 2)
    (hi : orderOf i = 2) (hiC : i ∈ centralizer ((E ⊔ L : Subgroup G) : Set G)) :
    ComponentTransfer.Setup t i L := by
  refine ⟨ht, hi, hc t htE (by intro h; simp [h] at ht), ?_⟩
  exact centralizer_le (show (zpowers t ⊔ L : Subgroup G) ≤ E ⊔ L from
    sup_le_sup (zpowers_le.mpr htE) le_rfl) hiC

/-- Sylow conjugacy takes an involution of C_G(L) into the fixed T_C,
using a conjugator which fixes L pointwise. -/
theorem exists_conjugate_mem_commutingSylow [Finite G]
    {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    {i : G} (hi : orderOf i = 2) (hiC : i ∈ centralizer (L : Set G)) :
    ∃ c : centralizer (L : Set G), MulAut.conj (c : G) i ∈ commutingSylow T L := by
  let C := centralizer (L : Set G)
  let a : C := ⟨i, hiC⟩
  have ha : orderOf a = 2 := (orderOf_coe a).symm.trans hi
  have hp : IsPGroup 2 (zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using ha
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨S, hS⟩ := h.exists_commutingSylow_of_normal hn
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C R S
  refine ⟨c, ?_⟩
  have hm : c * a * c⁻¹ ∈ (S : Subgroup C) := by
    rw [← hc]
    exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hR (mem_zpowers a))
  have hmT : MulAut.conj (c : G) i ∈ (T : Subgroup G) := by
    rw [hS] at hm
    exact hm
  exact ⟨hmT, (c * a * c⁻¹).property⟩

/-- The required 16.3.4 setup after interchanging the two involutions
and conjugating the enlargement into position. -/
theorem exists_exclusionSetup [Finite G]
    {T : Sylow 2 G} {z : G} {L I : Subgroup G} {t i : G}
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (hs : ComponentTransfer.Setup t i L)
    (hI : IsCentralizerComponent i I)
    (hLI : Theory.GroupTheory.IsComponentIn L (I ⊓ involutionCentralizer t))
    (hcomm : ⁅I, zpowers t⁆ = I) :
    ∃ (c : centralizer (L : Set G)),
      ExclusionSetup T z L (I.map (MulAut.conj (c : G)).toMonoidHom)
        (MulAut.conj (c : G) i) (MulAut.conj (c : G) t) := by
  have hiC : i ∈ centralizer (L : Set G) := centralizer_le (show L ≤ zpowers t ⊔ L from le_sup_right) hs.centralizes
  obtain ⟨c, hc⟩ := exists_conjugate_mem_commutingSylow h hn hs.involution_i hiC
  let e : G ≃* G := MulAut.conj (c : G)
  have hL : L.map e.toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ c.property)
  have hIC : IsCentralizerComponent (e i) (I.map e.toMonoidHom) := by
    have hm := (show Theory.GroupTheory.IsComponentIn I (involutionCentralizer i) from hI).map e
    change Theory.GroupTheory.IsComponentIn _ _
    simpa only [involutionCentralizer, map_centralizer_equiv, Set.image_singleton] using hm
  have hLC : Theory.GroupTheory.IsComponentIn L
      (I.map e.toMonoidHom ⊓ involutionCentralizer (e t)) := by
    have hm := hLI.map e
    simpa only [hL, Subgroup.map_inf _ _ e.toMonoidHom (by simpa using e.injective), involutionCentralizer,
      map_centralizer_equiv, Set.image_singleton] using hm
  have htC : t ∈ centralizer ((L ⊔ zpowers i : Subgroup G) : Set G) := by
    have hsup : L ⊔ zpowers i ≤ involutionCentralizer t := by
      refine sup_le hs.component.1 (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hs.centralizes t
          ((le_sup_left : zpowers t ≤ zpowers t ⊔ L) (mem_zpowers t))).symm
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hsup hx)
  have htC' : e t ∈ centralizer ((L ⊔ zpowers (e i) : Subgroup G) : Set G) := by
    have hm := mem_map_of_mem e.toMonoidHom htC
    rw [map_centralizer_equiv] at hm
    change e t ∈ centralizer ((L ⊔ zpowers i).map e.toMonoidHom : Set G) at hm
    simpa only [Subgroup.map_sup, hL, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] using hm
  have hcomm' : ⁅I.map e.toMonoidHom, zpowers (e t)⁆ = I.map e.toMonoidHom := by
    simpa only [map_commutator, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] using congrArg (Subgroup.map e.toMonoidHom) hcomm
  exact ⟨c, h, hn, (e.orderOf_eq i).trans hs.involution_i, hc, hIC,
    (e.orderOf_eq t).trans hs.involution_t, hLC, htC', hcomm'⟩

/-- Transport the full excluded simple groups, without replacing them by quotients. -/
theorem excluded_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsExcludedSimple A) : IsExcludedSimple B := by
  rcases h with ⟨n, hn, hU⟩ | hM | hJ | hH | hR
  · exact Or.inl ⟨n, hn, hU.of_mulEquiv e.symm⟩
  · exact Or.inr (Or.inl (hM.map (e.symm.trans ·)))
  · exact Or.inr (Or.inr (Or.inl (hJ.map (e.symm.trans ·))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hH.map (e.symm.trans ·)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hR.map (e.symm.trans ·)))))

/-- The specialized use of 16.3.4 in 16.3.5. The general-K version of
16.3.5 is not inferred from the distinguished-component hypothesis. -/
theorem not_excluded_of_exclusion [Finite G]
    {T : Sylow 2 G} {z : G} {L I : Subgroup G} {t i : G}
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (exclude : ∀ (J : Subgroup G) (a b : G),
      ExclusionSetup T z L J a b → ¬ IsExcludedSimple J)
    (hs : ComponentTransfer.Setup t i L)
    (hI : IsCentralizerComponent i I)
    (hLI : Theory.GroupTheory.IsComponentIn L (I ⊓ involutionCentralizer t))
    (hcomm : ⁅I, zpowers t⁆ = I) : ¬ IsExcludedSimple I := by
  intro hmodel
  obtain ⟨c, hc⟩ := exists_exclusionSetup h hn hs hI hLI hcomm
  exact exclude _ _ _ hc (excluded_of_equiv ((MulAut.conj (c : G)).subgroupMap I) hmodel)

/-- Nontriviality of the actual two-core follows from the full-group exclusion.
The quotient is identified with the original group only in the contrary case. -/
theorem twoCore_ne_bot_of_exclusion [Finite G]
    {T : Sylow 2 G} {z : G} {L I : Subgroup G} {t i : G}
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (exclude : ∀ (J : Subgroup G) (a b : G),
      ExclusionSetup T z L J a b → ¬ IsExcludedSimple J)
    (hs : ComponentTransfer.Setup t i L)
    (hI : IsCentralizerComponent i I)
    (hLI : Theory.GroupTheory.IsComponentIn L (I ⊓ involutionCentralizer t))
    (hcomm : ⁅I, zpowers t⁆ = I)
    (hmodel : IsExcludedSimple (I ⧸ pCore 2 I)) : pCore 2 I ≠ ⊥ := by
  intro hbot
  let e : (I ⧸ pCore 2 I) ≃* I :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact not_excluded_of_exclusion h hn exclude hs hI hLI hcomm
    (excluded_of_equiv e hmodel)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
