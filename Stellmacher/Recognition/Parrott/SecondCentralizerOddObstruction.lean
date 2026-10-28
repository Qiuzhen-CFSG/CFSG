module

public import Stellmacher.Recognition.Parrott.SecondCentralizerLocalStructure
public import Stellmacher.Recognition.Parrott.DerivedConjugacyCensus
public import Theory.GroupTheory.NormalOddKleinFourCentralization
public import Theory.PPrimeCore

/-!
# Odd subgroups of the second involution centralizer

Let N=N_G(F), K=O₂(N), and ZK be the ambient image of Z(K). Every odd
subgroup of C_G(v) normalized by ZK is trivial. In particular, C_G(v)
has trivial odd core, without assuming that C_G(v) lies in N.

The N-orbit of z has three points, because C_N(z) is the supplied Sylow
two-subgroup of order 2048 and N has order 6144. These are exactly the
nonidentity points of ZK. Conjugation therefore transports ZK≤O₂(C_G(z))
to the full centralizer of each of its involutions. The normal odd
Klein-four centralization theorem, with normalizing group ZK itself,
forces the given odd subgroup to centralize ZK. It then lies in
C_G(z)∩C_G(v), whose order is a power of two by the derived-core census.
The final odd-core application uses normality only inside C_G(v).

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, p.682, opening paragraph.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

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

private theorem center_nonidentity_conjugate
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    ∀ w ∈ Z, w ≠ 1 → ∃ g : N, (g : G) * z * (g : G)⁻¹ = w := by
  intro N K Z
  let _ := conjMulDistribMulActionOfLeNormalizer N Z d.normalizer_core_centers_normalized.1
  let zZ : Z := ⟨z, d.z_mem_normalizer_core_center⟩
  have hz1 : zZ ≠ 1 := by
    intro he
    have hh := congrArg Z.subtype he
    have ho := h.involution
    change z = 1 at hh
    simp [hh] at ho
  have hstab : MulAction.stabilizer N zZ = (d.sylow : Subgroup G).subgroupOf N := by
    ext n
    change n • zZ = zZ ↔ (n : G) ∈ (d.sylow : Subgroup G)
    rw [Subtype.ext_iff]
    change (n : G) * z * (n : G)⁻¹ = z ↔ _
    rw [mul_inv_eq_iff_eq_mul, ← mem_centralizer_singleton_iff,
      ← d.normalizer_inf_centralizer h]
    exact (and_iff_right n.property).symm
  have hstabcard : Nat.card (MulAction.stabilizer N zZ) = 2048 := by
    rw [hstab, Nat.card_congr (subgroupOfEquivOfLe d.sylow_le_normalizer).toEquiv]
    exact d.sylow_card h
  have hcount : Nat.card (MulAction.orbit N zZ) *
      Nat.card (MulAction.stabilizer N zZ) = Nat.card N := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N zZ)
  rw [hstabcard, (d.normalizer_core_order h hN hproper).1] at hcount
  have hthree : (MulAction.orbit N zZ).ncard = 3 := by
    change Nat.card (MulAction.orbit N zZ) = 3
    omega
  have hsub : MulAction.orbit N zZ ⊆ ({1} : Set Z)ᶜ := by
    rintro y ⟨g, rfl⟩
    change g • zZ ≠ (1 : Z)
    intro he
    exact hz1 ((MulDistribMulAction.toMulAut N Z g).injective
      (he.trans (map_one _).symm))
  have hcard : Nat.card Z = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  have hcompl : (({1} : Set Z)ᶜ).ncard = 3 := by
    rw [Set.ncard_compl, hcard, Set.ncard_singleton]
  have horbit : MulAction.orbit N zZ = ({1} : Set Z)ᶜ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcompl, hthree])
  intro w hw hw1
  have hwO : (⟨w, hw⟩ : Z) ∈ MulAction.orbit N zZ := by
    rw [horbit]
    exact fun he => hw1 (congrArg Z.subtype he)
  obtain ⟨g, hg⟩ := hwO
  exact ⟨g, congrArg Z.subtype hg⟩

private theorem center_le_involution_cores
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let Z := (center K).map (N.subtype.comp K.subtype)
    ∀ w ∈ Z, w ≠ 1 → Z ≤ (pCore 2 (centralizer ({w} : Set G))).map
      (centralizer ({w} : Set G)).subtype := by
  intro N K Z w hw hw1
  obtain ⟨g, hg⟩ := d.center_nonidentity_conjugate h hN hproper w hw hw1
  let f := MulAut.conj (g : G)
  let H := centralizer ({z} : Set G)
  let C := centralizer ({f z} : Set G)
  let e : H ≃* C := (f.subgroupMap H).trans
    (MulEquiv.subgroupCongr (map_element_centralizer f z))
  have hcore := pCore_map_iso 2 e
  have hfZ : Z.map f.toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizer_core_centers_normalized.1 g.property)
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

/-- An odd subgroup of the second centralizer normalized by the central
four-group is trivial. No containment of the ambient centralizer in N is assumed. -/
public theorem second_centralizer_odd_subgroup_eq_bot
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let ZK := (center K).map (N.subtype.comp K.subtype)
    ∀ O : Subgroup G, O ≤ centralizer ({v} : Set G) → Odd (Nat.card O) →
      ZK ≤ normalizer (O : Set G) → O = ⊥ := by
  intro N K ZK O hOC hodd hZO
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hZcard : Nat.card ZK = 4 :=
    (card_map_of_injective (K := center K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
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
      (d.center_le_involution_cores h hN hproper)
  have hOH : O ≤ H := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((hOZ hx) z d.z_mem_normalizer_core_center).symm
  obtain ⟨hvZ, hvout, _, _, _⟩ := d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix
  have hvE : v ∈ E := (d.normalizer_core_omega_center_le_inf h hN hproper hvZ).1
  have hvz : v ∉ zpowers z := fun hh => hvout
    ((zpowers_le.mpr d.z_mem_normalizer_core_center) hh)
  have hp := derived_centralizer_isTwoGroup h v hvE hvz
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdis : O ⊓ (H ⊓ centralizer ({v} : Set G)) = ⊥ :=
    (disjoint_of_coprime_natCard (by
      rw [hn]
      exact hodd.coprime_two_right.pow_right n)).eq_bot
  apply bot_unique
  rw [← hdis]
  exact le_inf le_rfl (le_inf hOH hOC)

/-- The full second involution centralizer has trivial odd core, before
establishing its containment in the second normalizer. -/
public theorem second_centralizer_pPrimeCore_eq_bot
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    pPrimeCore 2 (centralizer ({v} : Set G)) = ⊥ := by
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let ZK := (center K).map (N.subtype.comp K.subtype)
  let C := centralizer ({v} : Set G)
  let O := (pPrimeCore 2 C).map C.subtype
  have hOC : O ≤ C := map_subtype_le _
  have hodd : Odd (Nat.card O) := by
    rw [card_map_of_injective C.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hCN : C ≤ normalizer (O : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pPrimeCore 2 C).le_normalizer_map C.subtype
  have hZC : ZK ≤ C := d.normalizer_core_center_le.trans
    (d.normalizer_core_omega_inclusions.1.trans
      (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.2.2)
  have hObot : O = ⊥ :=
    d.second_centralizer_odd_subgroup_eq_bot h hN hproper Q v hv hfix O hOC hodd
      (hZC.trans hCN)
  exact (map_injective C.subtype_injective) (hObot.trans (map_bot C.subtype).symm)

end Stellmacher.Recognition.ParrottSecondElementaryData
