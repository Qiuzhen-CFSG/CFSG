module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.Transitivity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeElementaryCentralizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Interface
public import Theory.GroupTheory.AbelianCentralizerNormalizer
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The characteristic elementary eight and its HS normalizer

The exact degree-100 ATLAS carrier has trivial center: its defining generator
product has one fixed letter, and the carrier is transitive. The certified
subgroup of order `2^9` is Sylow. Its exhaustive normal elementary catalogue
makes the largest elementary subgroup characteristic, so its full normalizer
is invariant under every automorphism stabilizing that Sylow subgroup.
The ambient centralizer is a two-group and supplies a normal self-centralizing
two-subgroup of the normalizer; hence the normalizer has characteristic two.

An inner involution fixing this Sylow pointwise comes from a central Sylow
involution. The checked eight-element catalogue identifies it with `e0`.
Thus the remaining generation calculation has one fixed representative.

Sources: GLS3, Table 5.3m, printed p.274, and the faithful action on
`Omega_1(4^3)` on p.306; Aschbacher–Smith 2.3.9(7), printed p.526.
The quotient action and generation with `C(e0)` are not asserted here.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.BlockNormalizer
open Subgroup EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 20000

private theorem fixed_ab : ∀ i : Fin 100,
    (generatorAElement * generatorBElement : Equiv.Perm (Fin 100)) i = i ↔ i = 3 := by
  apply allFin
  decide +kernel

private theorem center_trivial_of_unique_fixed (w : Carrier) (v : Fin 100)
    (hw : ∀ i : Fin 100, (w : Equiv.Perm (Fin 100)) i = i ↔ i = v) :
    center Carrier = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  rw [mem_bot]
  have hc (g : Carrier) : g * z = z * g := mem_center_iff.mp hz g
  have hfix : (z : Equiv.Perm (Fin 100)) v = v := by
    apply (hw _).mp
    have h := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) v) (hc w)
    change (w : Equiv.Perm (Fin 100)) ((z : Equiv.Perm (Fin 100)) v) =
      (z : Equiv.Perm (Fin 100)) ((w : Equiv.Perm (Fin 100)) v) at h
    rwa [(hw v).mpr rfl] at h
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier v i
  change (g : Equiv.Perm (Fin 100)) v = i at hg
  have h := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) v) (hc g)
  change (g : Equiv.Perm (Fin 100)) ((z : Equiv.Perm (Fin 100)) v) =
    (z : Equiv.Perm (Fin 100)) ((g : Equiv.Perm (Fin 100)) v) at h
  rw [hfix, hg] at h
  exact h.symm

/-- Centerlessness of the exact degree-100 carrier, without a simplicity assumption. -/
theorem center_carrier_eq_bot : center Carrier = ⊥ :=
  center_trivial_of_unique_fixed (generatorAElement * generatorBElement) 3 fixed_ab

/-- The marked subgroup has odd index in the exact carrier. -/
theorem not_two_dvd_index : ¬ 2 ∣ subgroup.index := by
  intro hi
  have hd : 1024 ∣ Nat.card Carrier := by
    rw [← subgroup.card_mul_index, EvenLocalCandidates.subgroup_card]
    exact Nat.mul_dvd_mul_left 512 hi
  rw [NormalizerIndex.card_carrier] at hd
  norm_num at hd

/-- The marked subgroup of order `2^9`, certified Sylow by the exact HS order. -/
noncomputable def baseSylow : Sylow 2 Carrier :=
  (IsPGroup.of_card EvenLocalCandidates.subgroup_card).toSylow not_two_dvd_index

/-- The characteristic elementary subgroup of order eight in the marked Sylow. -/
abbrev baseElementary : Subgroup Carrier := elementary 2

/-- The full normalizer of the characteristic elementary eight, inside the exact HS carrier. -/
abbrev baseNormalizer : Subgroup Carrier := localGroup 2

private def conjugateIndex : Fin 3 → Fin 3 → Fin 8 := ![![1, 3, 4], ![1, 2, 7], ![1, 3, 4]]

private theorem conjugate_generator (i j : Fin 3) :
    sylowGenerator i * elementaryGenerator j * (sylowGenerator i)⁻¹ =
      small (conjugateIndex i j) := by
  have h : ∀ (i j : Fin 3) (x : Fin 100),
      ((sylowGenerator i * elementaryGenerator j * (sylowGenerator i)⁻¹ : Carrier) :
        Equiv.Perm (Fin 100)) x =
      (small (conjugateIndex i j) : Equiv.Perm (Fin 100)) x := by
    apply allFin₃
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i j))
/-- The concrete Sylow conjugation action on the three elementary generators.
This table supplies the upper-unitriangular part of the remaining normalizer action calculation. -/
theorem baseSylow_conjugation (i j : Fin 3) :
    sylowGenerator i * elementaryGenerator j * (sylowGenerator i)⁻¹ =
      small (![![1, 3, 4], ![1, 2, 7], ![1, 3, 4]] i j) :=
  conjugate_generator i j

/-- The marked Sylow subgroup normalizes its characteristic elementary eight. -/
theorem baseSylow_le_normalizer : (baseSylow : Subgroup Carrier) ≤ baseNormalizer := by
  change closure (Set.range sylowGenerator) ≤ normalizer (elementary 2 : Set Carrier)
  apply (closure_le _).mpr
  rintro g ⟨i, rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rw [elementary, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    change sylowGenerator i * elementaryGenerator j * (sylowGenerator i)⁻¹ ∈ elementary 2
    rw [conjugate_generator]
    exact small_mem_elementary _ 2 (conjugateIndex i j).isLt
  · exact le_of_eq (Nat.card_congr ((MulAut.conj (sylowGenerator i)).subgroupMap
      (elementary 2)).toEquiv)
/-- Normality here is relative to the marked Sylow subgroup. -/
instance baseElementary_normal : (baseElementary.subgroupOf subgroup).Normal :=
  (normal_subgroupOf_iff_le_normalizer (elementary_le_subgroup 2)).mpr baseSylow_le_normalizer
private theorem baseElementary_subgroupOf_ne_bot : baseElementary.subgroupOf subgroup ≠ ⊥ := by
  intro h
  have he := congrArg (Subgroup.map subgroup.subtype) h
  rw [map_subgroupOf_eq_of_le (elementary_le_subgroup 2), Subgroup.map_bot] at he
  exact elementary_ne_bot 2 he
/-- The exhaustive normal elementary catalogue makes its largest entry characteristic. -/
instance baseElementary_characteristic : (baseElementary.subgroupOf subgroup).Characteristic := by
  let := elementary_isElementaryAbelian 2
  let : IsElementaryAbelian 2 (baseElementary.subgroupOf subgroup) :=
    IsElementaryAbelian.subgroupOf (elementary_le_subgroup 2)
  apply characteristic_iff_map_le.mpr
  intro φ
  let A := (baseElementary.subgroupOf subgroup).map φ.toMonoidHom
  have hn : A.Normal := Subgroup.Normal.map inferInstance φ.toMonoidHom φ.surjective
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hne : A ≠ ⊥ := fun h => baseElementary_subgroupOf_ne_bot
    ((map_eq_bot_iff_of_injective _ φ.injective).mp h)
  obtain ⟨i, hi⟩ := normal_elementary_catalogue A hne hn inferInstance
  intro x hx
  have hm : (x : Carrier) ∈ elementary i := hi ▸ mem_map_of_mem subgroup.subtype hx
  exact (closure_mono (Set.image_mono (by intro j hj; exact Fin.le_last j))) hm

/-- The marked normalizer has characteristic two. -/
theorem baseNormalizer_selfCentralizing :
    centralizer (pCore 2 baseNormalizer : Set baseNormalizer) ≤ pCore 2 baseNormalizer := by
  let := elementary_isElementaryAbelian 2
  obtain ⟨Q, hn, hp, hc⟩ :=
    Theory.GroupTheory.exists_normal_selfCentralizing_pSubgroup_of_abelian_centralizer
      baseElementary (large_elementary_centralizer_isPGroup 2 (by decide))
  have hQ : Q ≤ pCore 2 baseNormalizer := le_sSup ⟨hn, hp⟩
  exact (centralizer_le hQ).trans (hc.trans hQ)

/-- Automorphisms stabilizing the marked Sylow preserve its characteristic elementary eight. -/
theorem baseElementary_invariant (β : MulAut Carrier) (hβ : subgroup.map β.toMonoidHom = subgroup) :
    baseElementary.map β.toMonoidHom = baseElementary := by
  let φ : MulAut subgroup := (β.subgroupMap subgroup).trans (MulEquiv.subgroupCongr hβ)
  have hφ := characteristic_iff_map_eq.mp baseElementary_characteristic φ
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    have hy' : (⟨y, elementary_le_subgroup 2 hy⟩ : subgroup) ∈
        baseElementary.subgroupOf subgroup := hy
    have hm := mem_map_of_mem φ.toMonoidHom hy'
    rw [hφ] at hm
    exact hm
  · exact le_of_eq (Nat.card_congr (β.subgroupMap baseElementary).toEquiv)

/-- Every ambient automorphism stabilizing the marked Sylow stabilizes its seed normalizer. -/
theorem baseNormalizer_invariant (β : MulAut Carrier)
    (hβ : subgroup.map β.toMonoidHom = subgroup) :
    baseNormalizer.map β.toMonoidHom = baseNormalizer := by
  change (normalizer (baseElementary : Set Carrier)).map β.toMonoidHom =
    normalizer (baseElementary : Set Carrier)
  rw [map_normalizer_eq_of_bijective _ β.bijective, baseElementary_invariant β hβ]

private theorem small_central_test : ∀ j : Fin 8,
    (s0 * small j : Equiv.Perm (Fin 100)) 1 =
        (small j * s0 : Equiv.Perm (Fin 100)) 1 →
    (s1 * small j : Equiv.Perm (Fin 100)) 1 =
        (small j * s1 : Equiv.Perm (Fin 100)) 1 →
    j = 0 ∨ j = 1 := by
  apply allFin
  decide +kernel

/-- The only inner involution fixing the marked Sylow pointwise is conjugation by `e0`. -/
theorem base_inner_eq_conj_e0 (α : MulAut Carrier)
    (hα : orderOf α = 2) (hi : α ∈ (MulAut.conj (G := Carrier)).range)
    (hfix : ∀ r ∈ (baseSylow : Subgroup Carrier), α r = r) :
    α = MulAut.conj e0 := by
  obtain ⟨a, ha, hαa, haR, hc⟩ := MulAut.inner_involution_fixing_sylow
    center_carrier_eq_bot baseSylow α hα (by
      obtain ⟨a, ha⟩ := hi
      exact ⟨a, ha.symm⟩) hfix
  obtain ⟨j, hj⟩ := small_of_normal_elementary_element a haR
    (ha ▸ pow_orderOf_eq_one a) (by
      intro g hg
      have he : g * a * g⁻¹ = a := by rw [← (hc g hg).eq]; simp
      rw [he])
  have hs0 : s0 ∈ subgroup := subset_closure ⟨0, rfl⟩
  have hs1 : s1 ∈ subgroup := subset_closure ⟨1, rfl⟩
  have ht := small_central_test j
    (by
      simpa only [hj, Subgroup.coe_mul] using congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100)) 1)
        (hc s0 hs0).eq.symm)
    (by
      simpa only [hj, Subgroup.coe_mul] using congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100)) 1)
        (hc s1 hs1).eq.symm)
  rcases ht with rfl | rfl
  · have ha1 : a = 1 := hj.symm
    simp [ha1] at ha
  · exact hαa.trans (congrArg MulAut.conj hj.symm)


private theorem small_point_injective : ∀ i j : Fin 8,
    (small i : Equiv.Perm (Fin 100)) 1 = (small j : Equiv.Perm (Fin 100)) 1 → i = j := by
  apply allFin₂
  decide +kernel

/-- The actual characteristic elementary subgroup has eight elements. -/
theorem baseElementary_card : Nat.card baseElementary = 8 := by
  let : IsElementaryAbelian 2 baseElementary := elementary_isElementaryAbelian 2
  let f : Fin 8 → baseElementary := fun j => ⟨small j, small_mem_elementary j 2 j.isLt⟩
  have hinj : Function.Injective f := by
    intro i j hij
    exact small_point_injective i j (congrArg
      (fun x : baseElementary => (x.val : Equiv.Perm (Fin 100)) 1) hij)
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨j, hj⟩ := small_of_normal_elementary_element a.val
      (elementary_le_subgroup 2 a.property)
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property) (by
        intro g hg
        have hm : g * a.val * g⁻¹ ∈ baseElementary :=
          baseElementary_normal.conj_mem ⟨a.val, elementary_le_subgroup 2 a.property⟩
            a.property ⟨g, hg⟩
        exact setLike_mul_comm a.property hm)
    exact ⟨j, Subtype.ext hj⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm.trans (Nat.card_fin 8)

end Sporadic.LeechRelated.HS.BlockNormalizer
