module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.PGroup.NormalEightFour
public import Theory.GroupTheory.NormalAbelianNoNormalEight

/-!
# Nonnormal quotient images without a normal elementary eight

The absence of normal elementary eights transfers along the canonical Sylow
embedding into the odd-core quotient. This gives the normal-only form of the
initial reduction in Janko–Thompson (1970), §4, p.389: the barred four lies in
the two-core, which has symplectic type and cyclic center. No bound on arbitrary
elementary subgroups is assumed. The quotient is exactly that defined in
`NormalFourOddCoreSetup`.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Central omega lies in a normal four under the normal-only rank bound. -/
public theorem centralOmega_le_normal_four (S : Sylow 2 G)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A) :
    centralOmega S ≤ E.map (S : Subgroup G).subtype :=
  map_mono (omega_one_center_le_normal_four_of_no_normal_eight hno E hE)

/-- Normal elementary subgroups in the odd-core quotient still have order below eight. -/
public theorem omegaQuotient_normal_elementary_card_lt_eight (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (U : Subgroup (OmegaQuotient S)) [U.Normal] [IsElementaryAbelian 2 U] :
    Nat.card U < 8 := by
  let f := omegaQuotientHom S
  have hU : U ≤ f.range := by
    rw [omegaQuotientHom_range]
    exact (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal _
  let F := U.comap f
  let e : F ≃* U := MulEquiv.ofBijective (f.subgroupComap U) ⟨by
    intro x y h
    exact Subtype.ext (omegaQuotientHom_injective S (congrArg Subtype.val h)), by
    intro u
    obtain ⟨x, hx⟩ := hU u.property
    exact ⟨⟨x, by change f x ∈ U; rw [hx]; exact u.property⟩, Subtype.ext hx⟩⟩
  have hFe : IsElementaryAbelian 2 F := {
    toIsMulCommutative := U.comap_injective_isMulCommutative (omegaQuotientHom_injective S)
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p 2 U }
  by_contra! h
  exact hno ⟨F, inferInstance, hFe, (Nat.card_congr e.toEquiv).symm ▸ h⟩

/-- The central involution survives in the quotient and belongs to the barred four. -/
public theorem fourImage_has_central_involution
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A) :
    ∃ t : OmegaQuotient S, orderOf t = 2 ∧ t ∈ fourImage S E ∧
      t ∈ center (OmegaQuotient S) := by
  let N := omegaNormalizer S
  let Z := (centralOmega S).subgroupOf N
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  have hZcard : Nat.card Z = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : centralOmega S ≤ N)).toEquiv,
      card_centralOmega, hZ]
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hi : Function.Injective (q.comp Z.subtype) :=
    injective_comp_subtype_of_coprime_ker q
      (by simpa only [q, QuotientGroup.ker_mk'] using
        (pPrimeCore_coprime_card (p := 2) (G := N))) Z hZp
  let e : Z ≃* Z.map q := MulEquiv.ofBijective (q.subgroupMap Z)
    ⟨fun x y h => hi (congrArg Subtype.val h), q.subgroupMap_surjective Z⟩
  have hcard : Nat.card (Z.map q) = 2 := (Nat.card_congr e.toEquiv).symm.trans hZcard
  let : Z.Normal := normal_in_normalizer
  let : (Z.map q).Normal := (inferInstance : Z.Normal).map q (QuotientGroup.mk'_surjective _)
  have hc : Z.map q ≤ center (OmegaQuotient S) := central_of_normal_card_two _ hcard
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Z.map q) 2 (by rw [hcard])
  refine ⟨t, (Subgroup.orderOf_coe t).trans ht, ?_, hc t.property⟩
  exact (map_mono (show Z ≤ (E.map (S : Subgroup G).subtype).subgroupOf N from
    fun x hx => centralOmega_le_normal_four S E hE hno hx)) t.property

/-- The barred normal Sylow four lies in the quotient two-core. -/
public theorem fourImage_le_pCore (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A) :
    fourImage S E ≤ pCore 2 (OmegaQuotient S) := by
  let : IsElementaryAbelian 2 (fourImage S E) := fourImage_elementary S E
  obtain ⟨t, ht, htE, htc⟩ := fourImage_has_central_involution S hZ E hE hno
  apply elementary_four_le_pCore_of_normalized_of_central_involution
    (omegaQuotient_centralizer_pCore_le hN S hZ) _ (fourImage_card S E hE) _ t ht htE htc
  have hnorm := E.le_normalizer_map (omegaQuotientHom S)
  rw [E.normalizer_eq_top, ← MonoidHom.range_eq_map, omegaQuotientHom_range,
    ← fourImage_eq_map] at hnorm
  exact (pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S)).trans hnorm

/-- The quotient two-core has symplectic type under the normal-only bound. -/
public theorem omegaQuotient_pCore_symplectic (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    IsBinarySymplecticType (pCore 2 (OmegaQuotient S)) := by
  apply IsPGroup.isBinarySymplecticType_of_characteristic_abelian pCore_isPGroup
  intro B hBc hBa
  let : B.Characteristic := hBc
  let : IsMulCommutative B := hBa
  apply isCyclic_characteristic_abelian_of_no_normal_four_or_eight _ pCore_isPGroup
  · intro D hDn hDe
    let : D.Normal := hDn
    let : IsElementaryAbelian 2 D := hDe
    exact omegaQuotient_normal_elementary_card_lt_eight S hno D
  · intro U hUn hUe
    let : U.Normal := hUn
    let : IsElementaryAbelian 2 U := hUe
    exact omegaQuotient_no_normal_four S E hunique hnormal U

/-- The center of the quotient two-core is cyclic under the normal-only bound. -/
public theorem omegaQuotient_pCore_center_isCyclic (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    IsCyclic (center (pCore 2 (OmegaQuotient S))) := by
  apply isCyclic_characteristic_abelian_of_no_normal_four_or_eight _ pCore_isPGroup
  · intro D hDn hDe
    let : D.Normal := hDn
    let : IsElementaryAbelian 2 D := hDe
    exact omegaQuotient_normal_elementary_card_lt_eight S hno D
  · intro U hUn hUe
    let : U.Normal := hUn
    let : IsElementaryAbelian 2 U := hUe
    exact omegaQuotient_no_normal_four S E hunique hnormal U

/-- The original normal four belongs to the preimage of the quotient two-core. -/
public theorem four_le_omegaCorePreimage (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A) :
    E ≤ omegaCorePreimage S := by
  apply map_le_iff_le_comap.mp
  rw [← fourImage_eq_map]
  exact fourImage_le_pCore hN S hZ E hE hno

/-- Nonnormality excludes a pure Hall factor, without bounding arbitrary
elementary subgroups. -/
public theorem omegaQuotient_pCore_not_hall (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hnormal : ¬ (fourImage S E).Normal) :
    ¬ IsBinaryHallFactor (pCore 2 (OmegaQuotient S)) := by
  let : IsElementaryAbelian 2 (fourImage S E) := fourImage_elementary S E
  exact not_isBinaryHallFactor_pCore_of_not_isPGroup (omegaQuotient_solvable hN S hZ)
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2) (omegaQuotient_not_isPGroup S E hnormal)
    (fourImage S E) (fourImage_le_pCore hN S hZ E hE hno)
    (fourImage_card S E hE) hnormal

/-- Hall's decomposition has a nontrivial extraspecial factor. Its width and
the size of the Hall factor still require the ambient argument. -/
public theorem omegaQuotient_pCore_factors (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    ∃ A D : Subgroup (pCore 2 (OmegaQuotient S)), A.Normal ∧ D.Normal ∧
      IsExtraspecial 2 A ∧ IsBinaryHallFactor D ∧
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) ∧ A ⊔ D = ⊤ := by
  obtain ⟨A, D, hAn, hDn, hA, hD, hc, hgen⟩ :=
    (omegaQuotient_pCore_symplectic S hno E hunique hnormal).exists_normal_factors
  have he : IsExtraspecial 2 A := by
    rcases hA with hA | hA
    · have hDt : D = ⊤ := by simpa only [hA, bot_sup_eq] using hgen
      exact (omegaQuotient_pCore_not_hall hN S hZ E hE hno hnormal
        (hD.of_mulEquiv ((MulEquiv.subgroupCongr hDt).trans Subgroup.topEquiv))).elim
    · exact hA
  exact ⟨A, D, hAn, hDn, he, hD, hc, hgen⟩

end Stellmacher.Recognition.NormalEightNonnormalImage
