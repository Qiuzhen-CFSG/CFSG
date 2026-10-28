module

public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaLocal
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaBounds
public import Theory.GroupTheory.CyclicFourExponentTwo
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Displacement on the supplied chosen omega subgroup

Put K = O₂(C_G(z)), E = K′, and S = C_G(z) ∩ C_G(a), retaining the
supplied a, fixed join F, Sylow subgroup, and element w. The supplied
index-two condition on Ω₁(S) gives |K ∩ S| = 64 and |S : K ∩ S| = 4.

The central commutator pairing gives [K,E] ≤ ⟨z⟩. Since K ∩ S properly
contains the self-centralizing F, its commutator with E ∩ F is nontrivial,
hence equals ⟨z⟩. In particular z belongs to S′. For any w in E, the
map s ↦ s⁻¹sʷ modulo S′ is a homomorphism with exponent-two image, and
it kills K ∩ S. The quotient S/(K ∩ S) is cyclic of order four. Every
square-one element has even image in this quotient, so its displacement
is trivial modulo S′. Closure then gives the same result on Ω₁(S).

This proves the needed commutator inclusion directly; neither the full
formula for S′ nor pointwise fixation of S′ is assumed. Source: Parrott,
*A characterization of the Tits' simple group* (1972), pp.673–674,
properties of the core, and p.676, the calculation [w,Ω₁(S)] ≤ S′.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem core_derived_commutator_bound (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ⁅K, E⁆ ≤ zpowers z := by
  intro H J K E
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  apply commutator_le.mpr
  intro b hb e he
  obtain ⟨bH, hbJ, rfl⟩ := hb
  obtain ⟨eJ, heJ, rfl⟩ := he
  let bJ : J := ⟨bH, hbJ⟩
  have heU : eJ ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ heJ
  have hec : ⁅eJ, bJ⁆ ∈ center J := by
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.mem_upperCentralSeries_succ_iff.mp heU bJ)
  have hbc : ⁅bJ, eJ⁆ ∈ center J := by
    simpa only [commutatorElement_inv] using (center J).inv_mem hec
  rw [← hZ]
  exact ⟨⁅bJ, eJ⁆, hbc, rfl⟩

private theorem chosen_z_mem_commutator_of_core_card
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    Nat.card (J.map H.subtype ⊓ S : Subgroup G) = 64 →
      z ∈ (commutator S).map S.subtype := by
  intro H J S hcard
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let B := J.map H.subtype ⊓ S
  let U := E ⊓ d.F
  have hbound : ⁅B, U⁆ ≤ zpowers z :=
    (commutator_mono inf_le_left inf_le_left).trans (core_derived_commutator_bound h)
  have hnontrivial : ⁅B, U⁆ ≠ ⊥ := by
    intro hbot
    have hBU : B ≤ centralizer (U : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp hbot
    have hBF : B ≤ d.F := by
      rw [← d.centralizer_eq]
      intro b hb
      have hCa : zpowers (d.a : G) ≤ centralizer ({b} : Set G) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hb.2.2).symm)
      have hCU : U ≤ centralizer ({b} : Set G) := by
        intro u hu
        exact mem_centralizer_singleton_iff.mpr (hBU hb u hu)
      have hF : d.F ≤ centralizer ({b} : Set G) := by
        rw [d.fixed_join, ← d.inf_eq]
        exact sup_le hCa hCU
      intro f hf
      exact mem_centralizer_singleton_iff.mp (hF hf)
    have hc := card_le_of_le hBF
    rw [d.card] at hc
    change Nat.card B = 64 at hcard
    omega
  have heq : ⁅B, U⁆ = zpowers z := by
    apply eq_of_le_of_card_ge hbound
    rw [Nat.card_zpowers, h.involution]
    exact (one_lt_card_iff_ne_bot _).mpr hnontrivial
  rw [map_subtype_commutator]
  apply commutator_mono (show B ≤ S from inf_le_right)
    (show U ≤ S from inf_le_right.trans d.le_chosen_centralizer)
  rw [heq]
  exact mem_zpowers z

/-- The local displacement calculation uses only the core intersection of
order 64 and the cyclic core quotient of order four. It holds for every
supplied derived-core element, including those in the fixed join. -/
public theorem chosen_square_one_displacement_of_core_geometry
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    Nat.card (K ⊓ S : Subgroup G) = 64 → K.relIndex S = 4 →
    ∀ (w : G) (hw : w ∈ E), ∀ v : S, v ^ 2 = 1 →
      v⁻¹ * S.normalizerMonoidHom
        ⟨w, d.chosen_derived_mem_normalizer h w hw⟩ v ∈ commutator S := by
  intro H J K E S hcard hindex w hw v hv
  let α := S.normalizerMonoidHom ⟨w, d.chosen_derived_mem_normalizer h w hw⟩
  let q : S →* Abelianization S := Abelianization.of
  let δ : S →* Abelianization S := q⁻¹ * q.comp α.toMonoidHom
  have hδ (s : S) : δ s = q (s⁻¹ * α s) := by
    simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
      map_mul, map_inv, MulEquiv.coe_toMonoidHom]
  have hzD : z ∈ (commutator S).map S.subtype :=
    chosen_z_mem_commutator_of_core_card d h hcard
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := ((commutator J).map J.subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, map_map] using hh
  have hδE (s : S) : ((s⁻¹ * α s : S) : G) ∈ E := by
    change (s : G)⁻¹ * (w * (s : G) * w⁻¹) ∈ E
    have hconj : (s : G)⁻¹ * w * (s : G) ∈ E :=
      by simpa only [SetLike.mem_coe, inv_inv] using
        ((hHE (H.inv_mem s.property.1)) w).mp hw
    simpa only [mul_assoc] using E.mul_mem hconj (E.inv_mem hw)
  have hsq (s : S) : (δ s) ^ 2 = 1 := by
    let : IsElementaryAbelian 2 (commutator J) :=
      (parrott_centralizer_structure z h).2.2.2.2.2.1
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
    have hh : (s⁻¹ * α s) ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hδE s)
    rw [hδ, ← map_pow, hh, map_one]
  have hkill (s : S) (hs : (s : G) ∈ K) : δ s = 1 := by
    have hc : ((s⁻¹ * α s : S) : G) ∈ zpowers z := by
      change (s : G)⁻¹ * (w * (s : G) * w⁻¹) ∈ zpowers z
      have hh := core_derived_commutator_bound h
        (commutator_mem_commutator (K.inv_mem hs) hw)
      simpa only [commutatorElement_def, inv_inv, mul_assoc] using hh
    have hm : s⁻¹ * α s ∈ commutator S :=
      (mem_map_iff_mem S.subtype_injective).mp ((zpowers_le.mpr hzD) hc)
    rw [hδ]
    apply MonoidHom.mem_ker.mp
    rwa [show q.ker = commutator S from Abelianization.ker_of S]
  let j : S →* H := inclusion inf_le_left
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' J).comp j)
  have hker : f.ker = K.subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' J (j s)) = 1 ↔ (s : G) ∈ K
    rw [← e.map_one, e.injective.eq_iff]
    change (QuotientGroup.mk' J) (j s) = 1 ↔ H.subtype (j s) ∈ J.map H.subtype
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact (mem_map_iff_mem H.subtype_injective).symm
  have hC : Nat.card f.range = 4 := by
    rw [← index_ker, hker]
    exact hindex
  have hp : IsPGroup 2 f.range :=
    (d.chosen_centralizer_isPGroup h).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : IsCyclic f.range :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ f.range hp).1
  have hkerδ : f.rangeRestrict.ker ≤ δ.ker := by
    intro s hs
    apply hkill
    have hs' : s ∈ f.ker := by
      exact congrArg Subtype.val (show f.rangeRestrict s = 1 from hs)
    rw [hker] at hs'
    exact hs'
  have heq : δ v = 1 := MonoidHom.eq_one_of_cyclic_four_of_square_eq_one f.rangeRestrict
    f.rangeRestrict_surjective hC δ hkerδ hsq v (by rw [← map_pow, hv, map_one])
  rw [hδ] at heq
  change v⁻¹ * α v ∈ commutator S
  rw [← show q.ker = commutator S from Abelianization.ker_of S]
  exact heq

/-- For every supplied w outside F, the index-two omega hypothesis forces
its displacement on each square-one element into the actual S′. -/
public theorem chosen_square_one_displacement_of_omega_index_two [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V.index = 2 → ∀ (w : G) (hw : w ∈ E), w ∉ d.F →
      ∀ v : S, v ^ 2 = 1 → v⁻¹ * S.normalizerMonoidHom
        ⟨w, d.chosen_derived_mem_normalizer h w hw⟩ v ∈ commutator S := by
  intro H E S V hindex w hw _hwF
  have hproper : V ≠ ⊤ := by
    intro ht
    rw [ht, index_top] at hindex
    omega
  obtain ⟨_, _, _, _, hi, hcard⟩ :=
    chosen_omega_geometry_of_ne_top hns hN d h hself hderived hconj hcenter hproper
  exact d.chosen_square_one_displacement_of_core_geometry h hcard hi w hw

/-- The displacement calculation on the entire actual omega subgroup,
with the supplied w, fixed join, and Sylow unchanged. -/
public theorem chosen_omega_displacement_of_index_two [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V.index = 2 → ∀ (w : G) (hw : w ∈ E), w ∉ d.F →
      ∀ v ∈ V, v⁻¹ * S.normalizerMonoidHom
        ⟨w, d.chosen_derived_mem_normalizer h w hw⟩ v ∈ commutator S := by
  intro H E S V hindex w hw hwF
  exact (d.chosen_omega_displacement_iff_square_one h w hw).mpr
    (chosen_square_one_displacement_of_omega_index_two
      hns hN d h hself hderived hconj hcenter hindex w hw hwF)

end Stellmacher.Recognition.ParrottSecondElementaryData
