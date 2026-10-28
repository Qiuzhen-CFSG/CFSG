module

public import Stellmacher.Recognition.NormalEightNonnormalSetup
public import Theory.GroupTheory.PGroup.CyclicCenterSymplecticBounds
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct
public import Theory.GroupTheory.SmallCoreSylowIndex

/-!
# Quotient-core bounds without a normal elementary eight

The quotient core is nonabelian, has order at least sixteen, and is proper
in the quotient Sylow. Once its order is less than thirty-two, the small-core
automorphism theorem gives relative Sylow index two and hence the exact
order/index pair `(16, 2)`.

The conditional assembly below separates the ambient width and tail exclusions.
It uses bounds only on normal elementary subgroups; it never assumes that an
arbitrary elementary eight is impossible. Width one means that every Hall
presentation has extraspecial factor of order eight. A noncyclic tail of
order eight would give an alternative presentation of width two.

Source: Janko–Thompson (1970), §4, printed pp.389–393. The Sylow normality
argument is adapted from `NormalFourNonnormalCoreBounds`.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The normal-only rank bound also applies to subgroups normalized by the
quotient Sylow; normality in the entire quotient is unnecessary. -/
public theorem omegaQuotient_sylow_normalized_elementary_card_lt_eight
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (U : Subgroup (OmegaQuotient S)) [IsElementaryAbelian 2 U]
    (hle : U ≤ omegaQuotientSylow S)
    (hnorm : (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) ≤ normalizer (U : Set (OmegaQuotient S))) :
    Nat.card U < 8 := by
  let f := omegaQuotientHom S
  have hrange : U ≤ f.range := by rwa [omegaQuotientHom_range]
  let F := U.comap f
  have hFn : F.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← U.comap_normalizer_eq_of_le_range hrange]
    intro x _
    exact hnorm (by rw [← omegaQuotientHom_range]; exact ⟨x, rfl⟩)
  let e : F ≃* U := MulEquiv.ofBijective (f.subgroupComap U) ⟨by
    intro x y h
    exact Subtype.ext (omegaQuotientHom_injective S (congrArg Subtype.val h)), by
    intro u
    obtain ⟨x, hx⟩ := hrange u.property
    exact ⟨⟨x, by change f x ∈ U; rw [hx]; exact u.property⟩, Subtype.ext hx⟩⟩
  have hFe : IsElementaryAbelian 2 F := {
    toIsMulCommutative := U.comap_injective_isMulCommutative (omegaQuotientHom_injective S)
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p 2 U }
  by_contra! h
  exact hno ⟨F, hFn, hFe, (Nat.card_congr e.toEquiv).symm ▸ h⟩

/-- The quotient Sylow cannot be normal when its unique normal four has
nonnormal ambient image. -/
public theorem omegaQuotientSylow_not_normal
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    ¬ (omegaQuotientSylow S : Subgroup (OmegaQuotient S)).Normal := by
  intro hT
  let T : Subgroup (OmegaQuotient S) := omegaQuotientSylow S
  let : T.Normal := hT
  let e : S ≃* T := omegaQuotientSylowEquiv S
  have hchar : E.Characteristic := characteristic_of_unique_normal_four E hE hunique
  let F := E.map e.toMonoidHom
  have hFchar : F.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro a
    rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(e.trans a |>.trans e.symm) y,
      characteristic_iff_le_comap.mp hchar _ hy, ?_⟩
    exact e.apply_symm_apply _
  let : F.Characteristic := hFchar
  have hmap : F.map T.subtype = fourImage S E := by
    change (E.map e.toMonoidHom).map T.subtype = fourImage S E
    rw [map_map, fourImage_eq_map]
    congr 1
    ext x
    exact omegaQuotientSylowEquiv_apply S x
  exact hnormal (hmap ▸ (inferInstance : (F.map T.subtype).Normal))

/-- The core cannot be abelian: its cyclic center would make it a Hall factor. -/
public theorem omegaQuotient_pCore_noncommutative (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    ¬ IsMulCommutative (pCore 2 (OmegaQuotient S)) := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  exact IsBinarySymplecticType.not_isMulCommutative_of_cyclic_center_not_hall
    (omegaQuotient_pCore_not_hall hN S hZ W hW hno hnormal)

/-- Hall's decomposition gives the lower bound without bounding nonnormal elementary subgroups. -/
public theorem omegaQuotient_pCore_card_lower (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    16 ≤ Nat.card (pCore 2 (OmegaQuotient S)) := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  exact IsBinarySymplecticType.sixteen_le_card_of_cyclic_center_not_hall pCore_isPGroup
    (omegaQuotient_pCore_symplectic S hno W hunique hnormal)
    (omegaQuotient_pCore_not_hall hN S hZ W hW hno hnormal)

/-- An upper bound on the core order is the only remaining input for the exact pair. -/
public theorem omegaQuotient_pCore_order_index_of_card_lt_thirty_two (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hbound : Nat.card (pCore 2 (OmegaQuotient S)) < 32) :
    Nat.card (pCore 2 (OmegaQuotient S)) = 16 ∧
      (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2 := by
  have hsmall : Nat.card (pCore 2 (OmegaQuotient S)) ≤ 16 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := OmegaQuotient S)).exists_card_eq
    have hnle : n ≤ 4 := by
      by_contra h
      have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 5 ≤ n by omega)
      rw [← hn] at hp
      norm_num at hp
      omega
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  exact ⟨Nat.le_antisymm hsmall
      (omegaQuotient_pCore_card_lower hN S hZ W hW hno hunique hnormal),
    (omegaQuotientSylow S).relIndex_pCore_eq_two_of_small_nonabelian
      (omegaQuotient_solvable hN S hZ)
      (omegaQuotient_centralizer_pCore_le hN S hZ)
      (omegaQuotient_pCore_noncommutative hN S hZ W hW hno hunique hnormal) hbound
      (omegaQuotientSylow_not_normal S W hW hunique hnormal)⟩

/-- Width one gives a nontrivial Hall tail and the exact central-product order formula. -/
public theorem omegaQuotient_pCore_factors_of_width_one (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A = 8) :
    ∃ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal ∧ D.Normal ∧ IsExtraspecial 2 A ∧ Nat.card A = 8 ∧
      IsBinaryHallFactor D ∧ D ≠ ⊥ ∧
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) ∧ A ⊔ D = ⊤ ∧
      Nat.card (pCore 2 (OmegaQuotient S)) = 4 * Nat.card D := by
  obtain ⟨A, D, hAn, hDn, hA, hD, hc, hg⟩ :=
    omegaQuotient_pCore_factors hN S hZ W hW hno hunique hnormal
  have hAc := hwidth A D hAn hDn hA hD hc hg
  have hDne : D ≠ ⊥ := by
    intro hDbot
    have hAtop : A = ⊤ := by simpa only [hDbot, sup_bot_eq] using hg
    have hlower := omegaQuotient_pCore_card_lower hN S hZ W hW hno hunique hnormal
    rw [hAtop, Nat.card_congr Subgroup.topEquiv.toEquiv] at hAc
    omega
  let : A.Normal := hAn
  let : D.Normal := hDn
  let : IsExtraspecial 2 A := hA
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  have hprod := card_mul_two_eq_of_extraspecial_of_cyclic_center pCore_isPGroup A D hDne hc hg
  rw [hAc] at hprod
  exact ⟨A, D, hAn, hDn, hA, hAc, hD, hDne, hc, hg, by omega⟩

/-- A noncyclic tail of order eight violates intrinsic width one. -/
public theorem omegaQuotient_noncyclicHallTail_card_ne_eight
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A = 8)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) : Nat.card D ≠ 8 := by
  intro hD
  let H := pCore 2 (OmegaQuotient S)
  let : IsCyclic (center H) := omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  obtain ⟨hH, hcard⟩ := extraspecial_card_thirty_two_of_noncyclic_eight_factors
    pCore_isPGroup A D hA hD hn hc hg
  have htop : IsExtraspecial 2 (⊤ : Subgroup H) := hH.of_mulEquiv Subgroup.topEquiv.symm
  have hbot : IsBinaryHallFactor (⊥ : Subgroup H) := Or.inl inferInstance
  have hh := hwidth ⊤ ⊥ inferInstance inferInstance htop hbot bot_le (top_sup_eq _)
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hcard] at hh
  contradiction

/-- The three ambient exclusions suffice for the required order/index pair.
The width premise rules out all larger extraspecial factors, not just one model. -/
public theorem omegaQuotient_pCore_order_index_of_width_and_tail_bounds (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A = 8)
    (hcyclic : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → Nat.card A = 8 →
      IsCyclic D → D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) →
      A ⊔ D = ⊤ → Nat.card D < 8)
    (hnoncyclic : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → Nat.card A = 8 →
      IsBinaryHallFactor D → ¬ IsCyclic D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) →
      A ⊔ D = ⊤ → Nat.card D < 16) :
    Nat.card (pCore 2 (OmegaQuotient S)) = 16 ∧
      (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2 := by
  apply omegaQuotient_pCore_order_index_of_card_lt_thirty_two hN S hZ W hW hno hunique hnormal
  obtain ⟨A, D, hAn, hDn, hA, hAc, hD, _, hc, hg, hcard⟩ :=
    omegaQuotient_pCore_factors_of_width_one hN S hZ W hW hno hunique hnormal hwidth
  have hsmall : Nat.card D < 8 := by
    by_cases hDc : IsCyclic D
    · exact hcyclic A D hAn hDn hA hAc hDc hc hg
    · have hlt := hnoncyclic A D hAn hDn hA hAc hD hDc hc hg
      let : A.Normal := hAn
      let : D.Normal := hDn
      let : IsExtraspecial 2 A := hA
      have hne := omegaQuotient_noncyclicHallTail_card_ne_eight
        S hno W hunique hnormal hwidth A D hAc hDc hc hg
      obtain ⟨n, hn⟩ :=
        ((pCore_isPGroup (p := 2) (G := OmegaQuotient S)).to_subgroup D).exists_card_eq
      have hnle : n ≤ 3 := by
        by_contra h
        have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ n by omega)
        rw [← hn] at hp
        norm_num at hp
        omega
      have hle : Nat.card D ≤ 8 := by
        rw [hn]
        exact Nat.pow_le_pow_right (by decide) hnle
      omega
  omega

end Stellmacher.Recognition.NormalEightNonnormalImage
