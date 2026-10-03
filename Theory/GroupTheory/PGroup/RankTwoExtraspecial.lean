module

public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PGroup.ExponentFourRankOne
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Models for extraspecial two-groups of elementary rank at most two

The models are the dihedral and quaternion groups of order eight and an
internal central product of a quaternion and a dihedral subgroup of order
eight. The embedded factors, their commutation, generation and intersection
of order two are retained. Their orders give the bound of thirty-two.

The reduction uses the exponent-four property of extraspecial two-groups.
A noncentral dihedral reflection commuting with a supplement excludes an
elementary four in that supplement, since their join would have order eight.

Sources: GLS2, Chapter C, Propositions 10.4–10.6; Gorenstein, *Finite Groups*,
Section 5.5. The reduction uses actual involutions rather than a convention
for the sign of the associated quadratic form.
-/

open Subgroup

/-- The three models, retaining the actual factors in the central-product case. -/
@[expose] public def IsRankTwoExtraspecialModel (P : Type*) [Group P] : Prop :=
  Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) ∨
    ∃ U V : Subgroup P, Nonempty (U ≃* QuaternionGroup 2) ∧
      Nonempty (V ≃* DihedralGroup 4) ∧
      V ≤ centralizer (U : Set P) ∧ U ⊔ V = ⊤ ∧ Nat.card (U ⊓ V : Subgroup P) = 2

/-- The order of any of the three models is at most thirty-two. -/
public theorem IsRankTwoExtraspecialModel.card_le
    {P : Type*} [Group P] [Finite P] (h : IsRankTwoExtraspecialModel P) :
    Nat.card P ≤ 32 := by
  rcases h with h | h | ⟨U, V, ⟨eU⟩, ⟨eV⟩, hc, hgen, hi⟩
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    decide
  · have hU : Nat.card U = 8 := by
      rw [Nat.card_congr eU.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hV : Nat.card V = 8 := by
      rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes U V
      (hc.trans (centralizer_le_normalizer _))
    rw [hU, hV, hi, hgen, Nat.card_congr Subgroup.topEquiv.toEquiv] at hprod
    omega

/-- A commuting involution outside a subgroup rules out elementary fours in
that subgroup when the ambient group has no elementary subgroup of order eight. -/
public theorem Subgroup.no_elementary_four_of_external_involution
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (C : Subgroup P) (t : P) (ht : t ^ 2 = 1) (hout : t ∉ C)
    (hc : t ∈ centralizer (C : Set P)) :
    ∀ E : Subgroup C, IsElementaryAbelian 2 E → Nat.card E ≠ 4 := by
  intro E hE hcard
  let : IsElementaryAbelian 2 E := hE
  let F := E.map C.subtype
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 (zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one ht
  have hcomm : zpowers t ≤ centralizer (F : Set P) :=
    zpowers_le.mpr (fun x hx => hc x (map_subtype_le E hx))
  let : IsElementaryAbelian 2 (F ⊔ zpowers t : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hsmall := hrank (F ⊔ zpowers t) inferInstance
  have hsize : Nat.card (F ⊔ zpowers t : Subgroup P) = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution F t ht
      (fun h => hout (map_subtype_le E h))
      (centralizer_le_normalizer _ (zpowers_le.mp hcomm)),
      card_map_of_injective C.subtype_injective, hcard]
  omega

/-- Without an elementary four, an extraspecial binary group is quaternion
of order eight. -/
public theorem IsExtraspecial.quaternion_two_of_no_elementary_four
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hfour : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E ≠ 4) :
    Nonempty (P ≃* QuaternionGroup 2) := by
  rcases (IsExtraspecial.isPGroup 2 P).isCyclic_or_quaternion_two_of_no_elementary_four
      IsExtraspecial.pow_four_eq_one hfour with h | h
  · let : IsCyclic P := h
    let : Nontrivial (P ⧸ center P) := IsExtraspecial.quotient_nontrivial 2 P
    have hc : center P = ⊤ := center_eq_top
    have hs : Subsingleton (P ⧸ center P) := QuotientGroup.subsingleton_iff.mpr hc
    exact (not_subsingleton (P ⧸ center P) hs).elim
  · exact h

/-- A dihedral central factor leaves a cyclic or quaternion supplement; the
cyclic case is absorbed by the dihedral factor. -/
public theorem IsExtraspecial.rankTwoModel_of_dihedral_factor
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (hZD : center P ≤ D) (hgen : D ⊔ centralizer (D : Set P) = ⊤) :
    IsRankTwoExtraspecialModel P := by
  let C := centralizer (D : Set P)
  let t : D := e.symm (DihedralGroup.sr 0)
  have ht : (t : P) ^ 2 = 1 := by
    have h : t ^ 2 = 1 := by
      apply e.injective
      simp only [map_pow, map_one, t, e.apply_symm_apply]
      decide
    exact congrArg Subtype.val h
  have htout : (t : P) ∉ C := by
    intro h
    have heq : (e.symm (DihedralGroup.r 1)) * t = t * (e.symm (DihedralGroup.r 1)) :=
      Subtype.ext (h _ (e.symm (DihedralGroup.r 1)).property)
    have hm := congrArg e heq
    simp only [map_mul, e.apply_symm_apply, t] at hm
    exact (by decide : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1) hm
  have hDC : D ≤ centralizer (C : Set P) := le_centralizer_iff.mp le_rfl
  have hfour := Subgroup.no_elementary_four_of_external_involution hrank C t ht htout
    (hDC t.property)
  have hpow (c : C) : c ^ 4 = 1 := Subtype.ext (IsExtraspecial.pow_four_eq_one (c : P))
  rcases ((IsExtraspecial.isPGroup 2 P).to_subgroup C).isCyclic_or_quaternion_two_of_no_elementary_four
      hpow hfour with hcyc | hquat
  · let : IsCyclic C := hcyc
    have hCZ : C ≤ center P := by
      have hh : (⊤ : Subgroup P) ≤ centralizer (C : Set P) := by
        rw [← hgen]
        exact sup_le hDC (le_centralizer C)
      have hh' := le_centralizer_iff.mp hh
      simpa only [coe_top, centralizer_univ] using hh'
    have hD : D = ⊤ := by
      have hh : D ⊔ C = D := sup_eq_left.mpr (hCZ.trans hZD)
      exact hh.symm.trans hgen
    exact Or.inl ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hD.symm).trans e)⟩
  · have hi : C ⊓ D = center P := by
      apply le_antisymm
      · have hDcentral : D ≤ centralizer ((C ⊓ D : Subgroup P) : Set P) :=
          le_centralizer_iff.mp (inf_le_left : C ⊓ D ≤ centralizer (D : Set P))
        have hCcentral : C ≤ centralizer ((C ⊓ D : Subgroup P) : Set P) :=
          le_centralizer_iff.mp (inf_le_right.trans hDC)
        have hh : (⊤ : Subgroup P) ≤ centralizer ((C ⊓ D : Subgroup P) : Set P) := by
          rw [← hgen]
          exact sup_le hDcentral hCcentral
        simpa only [coe_top, centralizer_univ] using (le_centralizer_iff.mp hh)
      · exact le_inf (center_le_centralizer _) hZD
    exact Or.inr (Or.inr ⟨C, D, hquat, ⟨e⟩, hDC, (sup_comm C D).trans hgen,
      by rw [hi]; exact IsExtraspecial.center_order_p 2 P⟩)

/-- An extraspecial two-group of elementary rank at most two is dihedral,
quaternion, or an actual internal central product of quaternion and dihedral
subgroups of order eight. -/
public theorem IsExtraspecial.rank_two_classification
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8) :
    Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) ∨
      ∃ U V : Subgroup P, Nonempty (U ≃* QuaternionGroup 2) ∧
        Nonempty (V ≃* DihedralGroup 4) ∧ V ≤ centralizer (U : Set P) ∧
        U ⊔ V = ⊤ ∧ Nat.card (U ⊓ V : Subgroup P) = 2 := by
  change IsRankTwoExtraspecialModel P
  by_cases hfour : ∃ E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 4
  · obtain ⟨E, hE, hcard⟩ := hfour
    let : IsElementaryAbelian 2 E := hE
    have hnot : ¬ E ≤ center P := by
      intro h
      have hc := card_le_of_le h
      rw [hcard, IsExtraspecial.center_order_p 2 P] at hc
      omega
    obtain ⟨t, ht, htZ⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨D, ⟨e⟩, hZD, hgen⟩ := IsExtraspecial.exists_dihedral_factor_of_noncentral_involution t
      (elemPow_eq_one_of_isElementaryAbelian t ht) htZ
    exact IsExtraspecial.rankTwoModel_of_dihedral_factor hrank D e hZD hgen
  · exact Or.inr (Or.inl (IsExtraspecial.quaternion_two_of_no_elementary_four
      (fun E hE hc => hfour ⟨E, hE, hc⟩)))

/-- The order bound accompanying the rank-two extraspecial classification. -/
public theorem IsExtraspecial.card_le_thirty_two_of_rank_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8) :
    Nat.card P ≤ 32 :=
  IsRankTwoExtraspecialModel.card_le (IsExtraspecial.rank_two_classification hrank)
