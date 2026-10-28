module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Existence
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Representative
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Centralizer

/-!
# Selecting the positive-three-rank component

The PSL₃(2) residual supplies a component of positive three-rank. Once
rank-one components are excluded, the ambient rank bound makes it rank two.
Two different rank-two components commute; the rank bound would then put an
elementary nine in one component's center. A center-rank bound excludes this,
so the positive-rank component is unique and hence normal. The quotient
layer is prime to three, forcing the simple residual into that component.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137. The rank-one exclusion is an explicit premise of
this conditional helper. `OddCenter` discharges its center-rank premise from
the local odd-core and residual models, without a multiplier assumption.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G] [Finite G]

private theorem rank_two_components_eq {K J : Subgroup G}
    (hK : IsComponent G K) (hJ : IsComponent G J)
    (hrank : primeRank 3 G ≤ 2) (hKr : 2 ≤ primeRank 3 K) (hJr : 2 ≤ primeRank 3 J)
    (hZ : primeRank 3 (center J) ≤ 1) : K = J := by
  by_contra hne
  have hcomm := commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne hJ hne)
  have hcomm' := commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hK (Ne.symm hne))
  obtain ⟨E, hE, hcard⟩ := CoverReduction.LocalCover.exists_elementary_nine hJr
  let := hE
  have hEZ : E ≤ center J := by
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    have hxp : x ^ 3 = 1 := congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 E) (⟨x, hx⟩ : E))
    have hxo : orderOf x = 3 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (orderOf_dvd_of_pow_eq_one hxp) with h | h
      · exact (hx1 (orderOf_eq_one_iff.mp h)).elim
      · exact h
    have hxG : orderOf (x : G) = 3 :=
      (orderOf_injective J.subtype J.subtype_injective x).trans hxo
    have hxK : (x : G) ∈ K := centralizing_three_mem hrank hKr hxG (hcomm' x.property)
    exact mem_center_iff.mpr (fun j => Subtype.ext (hcomm hxK j j.property))
  let A := E.subgroupOf (center J)
  let e : A ≃* E := subgroupOfEquivOfLe hEZ
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.subgroupOf hEZ
  have hAc : Nat.card A = 3 ^ 2 := (Nat.card_congr e.toEquiv).trans hcard
  have h := IsElementaryAbelian.primeRank_ge_of_card A hAc
  have hle := primeRank_le_of_injective 3 A.subtype A.subtype_injective
  omega

omit [Finite G] in
private theorem componentLayer_eq_iSup :
    componentLayer G = ⨆ i : {K : Subgroup G // IsComponent G K}, i.val := by
  apply le_antisymm
  · exact sSup_le fun J hJ => le_iSup (fun i : {K : Subgroup G // IsComponent G K} => i.val) ⟨J, hJ⟩
  · exact iSup_le fun i => le_sSup i.property

private theorem layer_quotient_prime_to_three {K : Subgroup G} [K.Normal]
    (hunique : ∀ J : Subgroup G, IsComponent G J → 0 < primeRank 3 J → J = K) :
    ¬ 3 ∣ Nat.card ((componentLayer G).map (QuotientGroup.mk' K)) := by
  classical
  let q := QuotientGroup.mk' K
  let C := {J : Subgroup G // IsComponent G J}
  have hn (i j : C) : i.val.map q ≤ normalizer (j.val.map q : Set (G ⧸ K)) := by
    by_cases he : i.val = j.val
    · rw [he]
      exact (j.val.map q).le_normalizer
    · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [← map_commutator, i.property.commutator_eq_bot_of_ne j.property he, Subgroup.map_bot]
  have hf (i : C) : ¬ 3 ∣ Nat.card (i.val.map q) := by
    by_cases hr : 0 < primeRank 3 i.val
    · have hi := hunique i.val i.property hr
      have hm : i.val.map q = ⊥ := by
        apply (Subgroup.map_eq_bot_iff _).mpr
        simpa only [q, QuotientGroup.ker_mk'] using hi.le
      simp [hm]
    · have hz : primeRank 3 i.val = 0 := by omega
      have hfree := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
      intro hd
      exact hfree (hd.trans (card_dvd_of_surjective (q.subgroupMap i.val) (q.subgroupMap_surjective i.val)))
  have h := not_dvd_card_iSup_of_normalizes (by decide : Nat.Prime 3) (fun i : C => i.val.map q) hn hf
  simpa only [componentLayer_eq_iSup, Subgroup.map_iSup] using h

private theorem simple_subgroup_le_component {F K : Subgroup G} [IsSimpleGroup F] [K.Normal]
    (hF : F ≤ componentLayer G) (hcard : 3 ∣ Nat.card F)
    (hunique : ∀ J : Subgroup G, IsComponent G J → 0 < primeRank 3 J → J = K) : F ≤ K := by
  let q := QuotientGroup.mk' K
  let φ := q.comp F.subtype
  rcases φ.normal_ker.eq_bot_or_eq_top with hb | ht
  · have hinj := φ.ker_eq_bot_iff.mp hb
    have hinj' : Function.Injective (q.subgroupMap F) := by
      intro x y h
      exact hinj (congrArg Subtype.val h)
    have hd := hcard.trans (card_dvd_of_injective (q.subgroupMap F) hinj')
    have hl := card_dvd_of_le (map_mono (f := q) hF)
    exact (layer_quotient_prime_to_three hunique (hd.trans hl)).elim
  · intro x hx
    have he : φ ⟨x, hx⟩ = 1 := by rw [φ.ker_eq_top_iff.mp ht]; rfl
    exact (QuotientGroup.eq_one_iff x).mp he

/-- Construct the unique positive-three-rank component and place the residual
inside it, conditional on rank-one exclusion and the component-center bound. -/
theorem selected_component_of_rank_conditions (L : Subgroup G) (f : G)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hF : fieldResidual L f ≤ componentLayer (centralizer ({f} : Set G)))
    (hrank : primeRank 3 (centralizer ({f} : Set G)) ≤ 2)
    (hno : ∀ J : Subgroup (centralizer ({f} : Set G)),
      IsComponent (centralizer ({f} : Set G)) J → primeRank 3 J ≠ 1)
    (hZ : ∀ J : Subgroup (centralizer ({f} : Set G)),
      IsComponent (centralizer ({f} : Set G)) J → primeRank 3 (center J) ≤ 1) :
    ∃ K : Subgroup (centralizer ({f} : Set G)),
      IsComponent (centralizer ({f} : Set G)) K ∧ K.Normal ∧ primeRank 3 K = 2 ∧
      fieldResidual L f ≤ K ∧
      ∀ J : Subgroup (centralizer ({f} : Set G)),
        IsComponent (centralizer ({f} : Set G)) J → 0 < primeRank 3 J → J = K := by
  obtain ⟨K, hK, hp⟩ := exists_positive_component_of_fieldResidual L f e hF
  have hKr : primeRank 3 K = 2 := by
    have hle := (primeRank_le_of_injective 3 K.subtype K.subtype_injective).trans hrank
    have hn := hno K hK
    omega
  have hu : ∀ J : Subgroup (centralizer ({f} : Set G)),
      IsComponent (centralizer ({f} : Set G)) J → 0 < primeRank 3 J → J = K := by
    intro J hJ hpJ
    have hJr : 2 ≤ primeRank 3 J := by have := hno J hJ; omega
    exact (rank_two_components_eq hK hJ hrank hKr.ge hJr (hZ J hJ)).symm
  have hn : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply hu _ (hK.map_conj g)
    rw [← primeRank_equiv 3 (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)]
    exact hp
  let := hn
  let : IsSimpleGroup (fieldResidual L f) := (MulEquiv.isSimpleGroup_congr
    (fieldResidualEquivModel L f e)).mpr (Atlas.psl_simple_high_rank 3 (by decide))
  have hFc : 3 ∣ Nat.card (fieldResidual L f) := by rw [fieldResidual_card L f e]; decide
  exact ⟨K, hK, hn, hKr, simple_subgroup_le_component hF hFc hu, hu⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
