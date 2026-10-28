module
public import Stellmacher.Recognition.Parrott.NormalizerFusion
public import Stellmacher.Recognition.Parrott.SecondCentralizerOddObstruction

/-!
# The second-centralizer odd obstruction from local normalizer data

The supplied three-group acts transitively on the three nonidentity elements
of the central four-group. Their involution centralizers therefore contain
that four-group in their two-cores. Coprime four-group action makes every
normalized odd subgroup centralize the four-group; the original derived
centralizer census then forces it to be trivial. The same three-group
conjugators show that each double centralizer with the fixed involution is a
two-group. No ambient N₂ or second-centralizer solvability is assumed.

Source: Parrott (1972), printed pp.682–683, Lemma 8. The genuine normalizer
fusion package supplies the earlier local construction without changing the
fixed involution or subgroup embeddings.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottNormalizerFusionData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

public theorem core_center_fusion_by_three
    (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    let A := (n.Q : Subgroup N).map N.subtype
    ∀ u ∈ Z, u ≠ 1 → ∃ a : A, (a : G) * z * (a : G)⁻¹ = u := by
  intro N K Z A
  have hAN : A ≤ N := map_subtype_le _
  let _ := conjMulDistribMulActionOfLeNormalizer A Z
    (hAN.trans d.normalizer_core_centers_normalized.1)
  let zZ : Z := ⟨z, d.z_mem_normalizer_core_center⟩
  have hz1 : zZ ≠ 1 := by
    intro he
    have hh := congrArg Z.subtype he
    have ho := h.involution
    change z = 1 at hh
    simp [hh] at ho
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans n.three_card
  have hdis : A ⊓ (d.sylow : Subgroup G) = ⊥ :=
    (disjoint_of_coprime_natCard (by rw [hAcard, d.sylow_card h]; decide)).eq_bot
  have hstab : MulAction.stabilizer A zZ = ⊥ := by
    apply bot_unique
    intro a ha
    have haC : (a : G) ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (congrArg Z.subtype ha))
    have haT : (a : G) ∈ (d.sylow : Subgroup G) :=
      d.normalizer_inf_centralizer h ▸ ⟨hAN a.property, haC⟩
    have ha1 : (a : G) ∈ (⊥ : Subgroup G) := hdis ▸ ⟨a.property, haT⟩
    exact Subtype.ext ha1
  have hcount : Nat.card (MulAction.orbit A zZ) *
      Nat.card (MulAction.stabilizer A zZ) = Nat.card A := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A zZ)
  rw [hstab, card_bot, mul_one, hAcard] at hcount
  have hsub : MulAction.orbit A zZ ⊆ ({1} : Set Z)ᶜ := by
    rintro y ⟨a, rfl⟩ he
    exact hz1 ((MulDistribMulAction.toMulAut A Z a).injective
      (he.trans (map_one _).symm))
  have hZcard : Nat.card Z = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      n.core_center_card
  have horbit : MulAction.orbit A zZ = ({1} : Set Z)ᶜ := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [Set.ncard_compl, Set.ncard_singleton, hZcard]
    change 4 - 1 ≤ Nat.card (MulAction.orbit A zZ)
    omega
  intro u hu hu1
  have huO : (⟨u, hu⟩ : Z) ∈ MulAction.orbit A zZ := by
    rw [horbit]
    exact fun he => hu1 (congrArg Z.subtype he)
  obtain ⟨a, ha⟩ := huO
  exact ⟨a, congrArg Z.subtype ha⟩


omit [Finite G] in
private theorem map_element_centralizer (f : G ≃* G) (x : G) :
    (centralizer ({x} : Set G)).map f.toMonoidHom =
      centralizer ({f x} : Set G) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({x} : Set G) f.toMonoidHom
  · intro y hy
    refine ⟨f.symm y, mem_centralizer_singleton_iff.mpr ?_, f.apply_symm_apply y⟩
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy


include n in
private theorem center_le_involution_cores
    (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    ∀ w ∈ Z, w ≠ 1 → Z ≤ (pCore 2 (centralizer ({w} : Set G))).map
      (centralizer ({w} : Set G)).subtype := by
  intro N K Z w hw hw1
  obtain ⟨g, hg⟩ := core_center_fusion_by_three n h w hw hw1
  let f := MulAut.conj (g : G)
  let H := centralizer ({z} : Set G)
  let C := centralizer ({f z} : Set G)
  let e : H ≃* C := (f.subgroupMap H).trans
    (MulEquiv.subgroupCongr (map_element_centralizer f z))
  have hcore := pCore_map_iso 2 e
  have hfZ : Z.map f.toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizer_core_centers_normalized.1 (map_subtype_le _ g.property))
  have hZcore : Z ≤ (pCore 2 H).map H.subtype :=
    d.normalizer_core_center_le.trans d.le_core
  change f z = w at hg
  rw [← hg]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hfZ.symm ▸ hx
  obtain ⟨yH, hyH, rfl⟩ := hZcore hy
  refine ⟨e yH, hcore ▸ mem_map_of_mem e.toMonoidHom hyH, ?_⟩
  rfl


private theorem derived_centralizer_isTwoGroup
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ v ∈ E, v ∉ zpowers z → IsPGroup 2 (H ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  intro H J E v hv hvz
  have hcard (x : G) (a : H) :
      Nat.card (H ⊓ centralizer ({(a : G) * x * (a : G)⁻¹} : Set G) : Subgroup G) =
        Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    let f := MulAut.conj (a : G)
    have hH : H.map f.toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer a.property)
    have hm : (H ⊓ centralizer ({x} : Set G)).map f.toMonoidHom =
        H ⊓ centralizer ({f x} : Set G) := by
      rw [map_inf _ _ _ f.injective, hH, map_element_centralizer]
    change Nat.card (H ⊓ centralizer ({f x} : Set G) : Subgroup G) = _
    rw [← hm, card_map_of_injective f.injective]
  obtain ⟨t, u, _, _, _, _, ht, hu, hcover⟩ := parrott_derived_conjugacy_census z h
  rcases hcover v hv hvz with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact IsPGroup.of_card (n := 10) ((hcard t a).trans ht)
  · exact IsPGroup.of_card (n := 9) ((hcard u a).trans hu)


public theorem odd_subgroup_eq_bot
    (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let ZK := (center K).map (N.subtype.comp K.subtype)
    ∀ O : Subgroup G, O ≤ centralizer ({n.v} : Set G) → Odd (Nat.card O) →
      ZK ≤ normalizer (O : Set G) → O = ⊥ := by
  intro N K ZK O hOC hodd hZO
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hZcard : Nat.card ZK = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      n.core_center_card
  let : IsElementaryAbelian 2 d.F := d.elementary
  let : IsElementaryAbelian 2 ZK := {
    toIsMulCommutative := map_isMulCommutative (center K) (N.subtype.comp K.subtype)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G)
        (d.normalizer_core_center_le x.property))) }
  let : Nontrivial ZK := Finite.one_lt_card_iff_nontrivial.mp (by rw [hZcard]; decide)
  let : IsKleinFour ZK := ⟨hZcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hOZ : O ≤ centralizer (ZK : Set G) :=
    normal_odd_centralizes_four_of_le_involution_cores ZK O ZK hZO hodd le_rfl
      (center_le_involution_cores n h)
  have hOH : O ≤ H := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((hOZ hx) z d.z_mem_normalizer_core_center).symm
  have hvE : n.v ∈ E := n.v_mem_inf.1
  have hvz : n.v ∉ zpowers z := fun hh => n.v_not_mem_core_center
    ((zpowers_le.mpr d.z_mem_normalizer_core_center) hh)
  have hp := derived_centralizer_isTwoGroup h n.v hvE hvz
  obtain ⟨r, hr⟩ := hp.exists_card_eq
  have hdis : O ⊓ (H ⊓ centralizer ({n.v} : Set G)) = ⊥ :=
    (disjoint_of_coprime_natCard (by
      rw [hr]
      exact hodd.coprime_two_right.pow_right r)).eq_bot
  apply bot_unique
  rw [← hdis]
  exact le_inf le_rfl (le_inf hOH hOC)



/-- The second centralizer intersects every nonidentity core-center centralizer
in a two-group, using the actual three-group conjugators. -/
public theorem core_center_double_centralizer_isTwoGroup
    (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    ∀ u ∈ Z, u ≠ 1 →
      IsPGroup 2 (centralizer ({n.v} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) := by
  intro N K Z u hu hu1
  have hvz : n.v ∉ zpowers z := fun hh => n.v_not_mem_core_center
    ((zpowers_le.mpr d.z_mem_normalizer_core_center) hh)
  have hp := derived_centralizer_isTwoGroup h n.v n.v_mem_inf.1 hvz
  obtain ⟨a, ha⟩ := core_center_fusion_by_three n h u hu hu1
  let e := MulAut.conj (a : G)
  have hev : e n.v = n.v := by
    change (a : G) * n.v * (a : G)⁻¹ = n.v
    exact mul_inv_eq_iff_eq_mul.mpr ((n.v_fixed) a a.property)
  have hez : e z = u := ha
  have hm : (centralizer ({z} : Set G) ⊓ centralizer ({n.v} : Set G) : Subgroup G).map e.toMonoidHom =
      centralizer ({u} : Set G) ⊓ centralizer ({n.v} : Set G) := by
    rw [map_inf _ _ _ e.injective, map_element_centralizer, map_element_centralizer, hez, hev]
  have hh := hp.map e.toMonoidHom
  change IsPGroup 2 ((centralizer ({z} : Set G) ⊓ centralizer ({n.v} : Set G) : Subgroup G).map e.toMonoidHom) at hh
  rw [hm, inf_comm] at hh
  exact hh

end Stellmacher.Recognition.ParrottNormalizerFusionData
