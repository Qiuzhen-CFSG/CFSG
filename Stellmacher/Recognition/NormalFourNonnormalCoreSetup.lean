module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.CharacteristicTwoCoreFour
public import Theory.GroupTheory.RankTwoNormalAbelian
public import Theory.GroupTheory.PGroup.RankTwoSymplecticType
public import Theory.GroupTheory.PGroup.RankTwoCoreHallExclusion
public import Theory.GroupTheory.PGroup.RankTwoExtraspecial

/-!
# The nonnormal four-group in the actual odd-core quotient

Let `N = N_G(Ω₁(Z(S)))` and `K = N/O₂′(N)`. The quotient map embeds
`S` as a Sylow subgroup of `K`, and every elementary subgroup of `K`
lifts through the odd kernel. Thus the ambient rank bound holds in `K`.
If the unique normal four of `S` has nonnormal image in `K`, then `K`
has no normal four-group. The image nevertheless lies in `O₂(K)`:
it contains the central involution and is normalized by the two-core.

Hall's theorem applies to `O₂(K)`, because a noncyclic characteristic
abelian subgroup would give an ambient normal four. Its extraspecial
factor is nontrivial and has one of the rank-two models, of order at most
32. These are the initial reductions of §4; the ambient fusion exclusions
needed to bound the entire Sylow group are not asserted here.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, pp.389–393, especially
p.389; `refs/original/n-group-global/odd-core-rank-two-source/normal-four-case-split.md`.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The actual quotient of the central-omega normalizer by its odd core. -/
public abbrev OmegaQuotient (S : Sylow 2 G) :=
  omegaNormalizer S ⧸ pPrimeCore 2 (omegaNormalizer S)

/-- The canonical map from the original Sylow subgroup to the odd-core quotient. -/
public def omegaQuotientHom (S : Sylow 2 G) : S →* OmegaQuotient S :=
  (QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))).comp
    (inclusion (sylow_le_omegaNormalizer S))

omit [Finite G] in
/-- The canonical Sylow map is the restriction of the actual quotient map. -/
public theorem omegaQuotientHom_apply (S : Sylow 2 G) (x : S) :
    omegaQuotientHom S x = QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))
      ⟨(x : G), sylow_le_omegaNormalizer S x.property⟩ := by
  unfold omegaQuotientHom
  rfl

/-- The odd kernel does not identify distinct Sylow elements. -/
public theorem omegaQuotientHom_injective (S : Sylow 2 G) :
    Function.Injective (omegaQuotientHom S) := by
  let N := omegaNormalizer S
  let P := (S : Subgroup G).subgroupOf N
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  have hP : IsPGroup 2 P :=
    S.isPGroup'.comap_of_injective N.subtype N.subtype_injective
  have hi := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := N))) P hP
  intro x y h
  have he := hi (a₁ := ⟨inclusion (sylow_le_omegaNormalizer S) x, x.property⟩)
    (a₂ := ⟨inclusion (sylow_le_omegaNormalizer S) y, y.property⟩) h
  exact Subtype.ext (congrArg (fun a : P => ((a : N) : G)) he)

/-- The image of the original Sylow subgroup in the actual quotient. -/
public def omegaQuotientSylow (S : Sylow 2 G) : Sylow 2 (OmegaQuotient S) :=
  (S.subtype (sylow_le_omegaNormalizer S)).mapSurjective
    (QuotientGroup.mk'_surjective (pPrimeCore 2 (omegaNormalizer S)))

/-- The quotient Sylow's underlying subgroup is the image of the normalizer Sylow. -/
public theorem omegaQuotientSylow_coe (S : Sylow 2 G) :
    (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) =
      (S.subtype (sylow_le_omegaNormalizer S) : Subgroup (omegaNormalizer S)).map
        (QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))) := by
  unfold omegaQuotientSylow
  rfl

/-- The canonical map has exactly the quotient Sylow as its range. -/
public theorem omegaQuotientHom_range (S : Sylow 2 G) :
    (omegaQuotientHom S).range = omegaQuotientSylow S := by
  rw [omegaQuotientHom, MonoidHom.range_comp, inclusion_range]
  rfl

omit [Finite G] in
/-- The prescribed barred four is the image under the canonical Sylow map. -/
public theorem fourImage_eq_map (S : Sylow 2 G) (E : Subgroup S) :
    fourImage S E = E.map (omegaQuotientHom S) := by
  rw [fourImage, omegaQuotientHom, ← map_map]
  congr 1
  apply (map_injective (omegaNormalizer S).subtype_injective)
  rw [map_subgroupOf_eq_of_le (four_le_omegaNormalizer S E), map_map]
  rfl

/-- The original Sylow subgroup and its quotient image are isomorphic. -/
public noncomputable def omegaQuotientSylowEquiv (S : Sylow 2 G) :
    S ≃* omegaQuotientSylow S :=
  (MonoidHom.ofInjective (omegaQuotientHom_injective S)).trans
    (MulEquiv.subgroupCongr (omegaQuotientHom_range S))

/-- The Sylow equivalence sends each element to its actual quotient image. -/
public theorem omegaQuotientSylowEquiv_apply (S : Sylow 2 G) (x : S) :
    (omegaQuotientSylowEquiv S x : OmegaQuotient S) = omegaQuotientHom S x := by
  unfold omegaQuotientSylowEquiv
  rfl

/-- The ambient elementary rank bound survives the odd-core quotient. -/
public theorem omegaQuotient_rank
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (A : Subgroup (OmegaQuotient S))
    [IsElementaryAbelian 2 A] : Nat.card A < 8 := by
  let N := omegaNormalizer S
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  obtain ⟨B, hBe, -, hc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    q (QuotientGroup.mk'_surjective _)
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := N))) A
  let : IsElementaryAbelian 2 B := hBe
  have h := hrank (B.map N.subtype) (IsElementaryAbelian.map _)
  rwa [card_map_of_injective N.subtype_injective, hc] at h

/-- A normal quotient four would pull back to the unique normal four of the Sylow. -/
public theorem omegaQuotient_no_normal_four
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (U : Subgroup (OmegaQuotient S)) [U.Normal] [IsElementaryAbelian 2 U] :
    Nat.card U ≠ 4 := by
  intro hc
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
  have heq : F = E := hunique F inferInstance hFe ((Nat.card_congr e.toEquiv).trans hc)
  have hmap : fourImage S E = U := by
    rw [fourImage_eq_map, ← heq]
    exact map_comap_eq_self hU
  exact hnormal (hmap ▸ inferInstance)

/-- The actual quotient is solvable by the N₂ hypothesis. -/
public theorem omegaQuotient_solvable (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2) :
    Group.IsSolvable (OmegaQuotient S) := by
  let : Group.IsSolvable (omegaNormalizer S) := omegaNormalizer_solvable hN S hZ
  infer_instance

/-- The two-core of the actual quotient is self-centralizing. -/
public theorem omegaQuotient_centralizer_pCore_le (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2) :
    centralizer (pCore 2 (OmegaQuotient S) : Set (OmegaQuotient S)) ≤
      pCore 2 (OmegaQuotient S) := by
  rw [← Fitting_eq_pcore (OmegaQuotient S) 2 (pPrimeCore_quotient_pPrimeCore_eq_bot 2)]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
    (omegaQuotient_solvable hN S hZ)

/-- The central involution survives in the quotient and belongs to the barred four. -/
public theorem fourImage_has_central_involution
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
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
    fun x hx => centralOmega_le_four hrank S E hE hx)) t.property

/-- The barred normal Sylow four lies in the quotient two-core. -/
public theorem fourImage_le_pCore (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    fourImage S E ≤ pCore 2 (OmegaQuotient S) := by
  let : IsElementaryAbelian 2 (fourImage S E) := fourImage_elementary S E
  obtain ⟨t, ht, htE, htc⟩ := fourImage_has_central_involution hrank S hZ E hE
  apply elementary_four_le_pCore_of_normalized_of_central_involution
    (omegaQuotient_centralizer_pCore_le hN S hZ) _ (fourImage_card S E hE) _ t ht htE htc
  have hnorm := E.le_normalizer_map (omegaQuotientHom S)
  rw [E.normalizer_eq_top, ← MonoidHom.range_eq_map, omegaQuotientHom_range,
    ← fourImage_eq_map] at hnorm
  exact (pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S)).trans hnorm

/-- Nonnormality of the barred four forces the quotient two-core to have symplectic type. -/
public theorem omegaQuotient_pCore_symplectic
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    IsBinarySymplecticType (pCore 2 (OmegaQuotient S)) := by
  apply IsPGroup.isBinarySymplecticType_of_characteristic_abelian pCore_isPGroup
  intro B hBc hBa
  let : B.Characteristic := hBc
  let : IsMulCommutative B := hBa
  apply isCyclic_characteristic_abelian_of_no_normal_four _ pCore_isPGroup
  · intro D hD _
    let : IsElementaryAbelian 2 D := hD
    exact omegaQuotient_rank hrank S D
  · intro U hU hUe
    let : U.Normal := hU
    let : IsElementaryAbelian 2 U := hUe
    exact omegaQuotient_no_normal_four S E hunique hnormal U

/-- The center of the actual quotient core is cyclic. -/
public theorem omegaQuotient_pCore_center_isCyclic
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    IsCyclic (center (pCore 2 (OmegaQuotient S))) := by
  apply isCyclic_characteristic_abelian_of_no_normal_four _ pCore_isPGroup
  · intro U hU _
    let : IsElementaryAbelian 2 U := hU
    exact omegaQuotient_rank hrank S U
  · intro U hU hUe
    let : U.Normal := hU
    let : IsElementaryAbelian 2 U := hUe
    exact omegaQuotient_no_normal_four S E hunique hnormal U

/-- The quotient cannot be a two-group when its Sylow four is nonnormal. -/
public theorem omegaQuotient_not_isPGroup (S : Sylow 2 G)
    (E : Subgroup S) [E.Normal] (hnormal : ¬ (fourImage S E).Normal) :
    ¬ IsPGroup 2 (OmegaQuotient S) := by
  intro hQ
  have htop : (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) = ⊤ :=
    top_unique ((hQ.to_subgroup ⊤).le_sylow_of_normal _)
  have hf : Function.Surjective (omegaQuotientHom S) :=
    MonoidHom.range_eq_top.mp ((omegaQuotientHom_range S).trans htop)
  rw [fourImage_eq_map] at hnormal
  exact hnormal ((inferInstance : E.Normal).map _ hf)

/-- The quotient two-core is not a pure cyclic or maximal-class Hall factor. -/
public theorem omegaQuotient_pCore_not_hall (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hnormal : ¬ (fourImage S E).Normal) :
    ¬ IsBinaryHallFactor (pCore 2 (OmegaQuotient S)) := by
  let : IsElementaryAbelian 2 (fourImage S E) := fourImage_elementary S E
  exact not_isBinaryHallFactor_pCore_of_not_isPGroup (omegaQuotient_solvable hN S hZ)
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2) (omegaQuotient_not_isPGroup S E hnormal)
    (fourImage S E) (fourImage_le_pCore hN hrank S hZ E hE)
    (fourImage_card S E hE) hnormal

/-- The quotient two-core has a nontrivial extraspecial factor of rank at most two. -/
public theorem omegaQuotient_pCore_factors (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    ∃ A D : Subgroup (pCore 2 (OmegaQuotient S)), A.Normal ∧ D.Normal ∧
      IsExtraspecial 2 A ∧ IsRankTwoExtraspecialModel A ∧ Nat.card A ≤ 32 ∧
      IsBinaryHallFactor D ∧ D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) ∧
      A ⊔ D = ⊤ := by
  obtain ⟨A, D, hAn, hDn, hA, hD, hc, hgen⟩ :=
    (omegaQuotient_pCore_symplectic hrank S E hunique hnormal).exists_normal_factors
  have he : IsExtraspecial 2 A := by
    rcases hA with hA | hA
    · have hDt : D = ⊤ := by simpa only [hA, bot_sup_eq] using hgen
      exact (omegaQuotient_pCore_not_hall hN hrank S hZ E hE hnormal
        (hD.of_mulEquiv ((MulEquiv.subgroupCongr hDt).trans Subgroup.topEquiv))).elim
    · exact hA
  let : IsExtraspecial 2 A := he
  have hrankQ (U : Subgroup (OmegaQuotient S)) (hU : IsElementaryAbelian 2 U) :
      Nat.card U < 8 := by
    let : IsElementaryAbelian 2 U := hU
    exact omegaQuotient_rank hrank S U
  have hmodel : IsRankTwoExtraspecialModel A := IsExtraspecial.rank_two_classification
    (elementary_card_lt_eight_of_subgroup
      (elementary_card_lt_eight_of_subgroup hrankQ (pCore 2 (OmegaQuotient S))) A)
  exact ⟨A, D, hAn, hDn, he, hmodel, hmodel.card_le, hD, hc, hgen⟩

/-- The part of the original Sylow lying over the actual quotient two-core. -/
public abbrev omegaCorePreimage (S : Sylow 2 G) : Subgroup S :=
  (pCore 2 (OmegaQuotient S)).comap (omegaQuotientHom S)

/-- The Sylow embedding maps the core preimage onto the entire quotient core. -/
public theorem omegaCorePreimage_map (S : Sylow 2 G) :
    (omegaCorePreimage S).map (omegaQuotientHom S) = pCore 2 (OmegaQuotient S) := by
  apply map_comap_eq_self
  rw [omegaQuotientHom_range]
  exact pCore_isPGroup.le_sylow_of_normal _

/-- The core preimage is an actual copy of the quotient two-core. -/
public noncomputable def omegaCorePreimageEquiv (S : Sylow 2 G) :
    omegaCorePreimage S ≃* pCore 2 (OmegaQuotient S) :=
  ((omegaCorePreimage S).equivMapOfInjective (omegaQuotientHom S)
    (omegaQuotientHom_injective S)).trans (MulEquiv.subgroupCongr (omegaCorePreimage_map S))

/-- The core preimage has the order of the quotient core. -/
public theorem card_omegaCorePreimage (S : Sylow 2 G) :
    Nat.card (omegaCorePreimage S) = Nat.card (pCore 2 (OmegaQuotient S)) :=
  Nat.card_congr (omegaCorePreimageEquiv S).toEquiv

/-- The index of the core preimage is the prescribed relative quotient index. -/
public theorem index_omegaCorePreimage (S : Sylow 2 G) :
    (omegaCorePreimage S).index =
      (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) := by
  rw [omegaCorePreimage, index_comap, omegaQuotientHom_range]

/-- The original normal four lies in the core preimage. -/
public theorem four_le_omegaCorePreimage (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    E ≤ omegaCorePreimage S := by
  apply map_le_iff_le_comap.mp
  rw [← fourImage_eq_map]
  exact fourImage_le_pCore hN hrank S hZ E hE

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
