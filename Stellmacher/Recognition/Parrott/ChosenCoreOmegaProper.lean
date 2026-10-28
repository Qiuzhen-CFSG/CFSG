module

public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaLocal
public import Stellmacher.Recognition.Parrott.ChosenCoreInvolutionContainment

/-!
# Properness of the chosen omega

Put S = C_G(z) ∩ C_G(a), K for the ambient two-core, and E for its derived
subgroup. If every square-one element of K ∩ S lies in the supplied F,
the image of Ω₁(S) modulo E is abelian. For mixed generators, the Sylow
normalizes F and hence fixes its order-two image modulo E. Two outer
involutions have the same image in the cyclic core quotient; their product
lies in K, so its square lies in E. The assertion extends to omega by closure.

In the index-two branch |K ∩ S| = 64 > |F|. Self-centralization of F puts
z in S′. If omega were S, the commutator containment would contradict the
characteristic-subgroup weak-closure obstruction. The index-four branch is
already closed by the cyclic quotient. The sum-free involution-coset calculation
in `ChosenCoreInvolutionContainment` discharges the local containment premise.
The final theorem retains the center-order-eight consumer's hypotheses and
supplied witnesses, although properness uses only the local data and fusion.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–676, especially the inference following “As 3 divides” on p.676.
The private z-membership argument is adapted from the existing proof in
`ChosenCoreCenterOrder`, without importing that module.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem commute_of_three_squares (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) :
    Commute x y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy)
  have hxyi : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hxy)
  simpa only [Commute, SemiconjBy, mul_inv_rev, hxi, hyi] using hxyi.symm

-- Normalizing the supplied join fixes its nontrivial image modulo E.
private theorem fixed_join_commute_mod_derived
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := (commutator J).map J.subtype
    let q := QuotientGroup.mk' D
    ∀ (x y : H), (x : G) ∈ d.F → (y : G) ∈ (d.sylow : Subgroup G) →
      Commute (q x) (q y) := by
  intro H J D q x y hx hy
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let FH := zpowers d.a ⊔ (D ⊓ centralizer ({d.a} : Set H))
  have hDmap : D.map H.subtype = E := map_map _ _ _
  have hfixed : (D ⊓ centralizer ({d.a} : Set H)).map H.subtype =
      E ⊓ centralizer ({(d.a : G)} : Set G) := by
    apply le_antisymm
    · rintro b ⟨c, hc, rfl⟩
      exact ⟨hDmap ▸ mem_map_of_mem H.subtype hc.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hc.2))⟩
    · rintro b ⟨⟨c, hc, rfl⟩, hb⟩
      exact ⟨(c : H), ⟨mem_map_of_mem J.subtype hc,
        mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp hb))⟩, rfl⟩
  have hFHmap : FH.map H.subtype = d.F := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfixed]
    exact d.fixed_join.symm
  have hFH : d.F.subgroupOf H = FH := by
    rw [← hFHmap]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hyN : y ∈ normalizer (FH : Set H) := by
    rw [← hFH, ← subgroupOf_normalizer_eq
      (d.le_sylow.trans d.sylow_le_centralizer)]
    exact d.sylow_le_normalizer hy
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map J.subtype
  rw [elementary_involution_fixed_join_normalizer D d.a d.a_order
    d.a_not_mem_derived] at hyN
  have hay : Commute (q d.a) (q y) :=
    (mem_centralizer_singleton_iff.mp hyN).symm
  have hle : FH ≤ (centralizer ({q y} : Set (H ⧸ D))).comap q := by
    apply sup_le
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hay)
    · intro b hb
      have hbq : q b = 1 := (QuotientGroup.eq_one_iff _).mpr hb.1
      change q b ∈ centralizer ({q y} : Set (H ⧸ D))
      rw [hbq]
      exact one_mem _
  exact mem_centralizer_singleton_iff.mp (hle (hFH ▸ hx))

/-- Once the core square-one elements lie in F, the chosen omega has abelian
image modulo the derived core. -/
public theorem chosen_omega_commutator_le_derived_of_core_involutions
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let U := (omega₁ S (p := 2)).map S.subtype
    (∀ x : G, x ∈ K ⊓ S → x ^ 2 = 1 → x ∈ d.F) → ⁅U, U⁆ ≤ E := by
  intro H J K E S U hcore
  let D := (commutator J).map J.subtype
  let q := QuotientGroup.mk' D
  let j : S →* H := inclusion inf_le_left
  let f := q.comp j
  let qJ := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let m := e.toMonoidHom.comp (qJ.comp j)
  let : Finite m.range := Finite.of_surjective m.rangeRestrict m.rangeRestrict_surjective
  have hp : IsPGroup 2 m.range :=
    (d.chosen_centralizer_isPGroup h).of_surjective m.rangeRestrict
      m.rangeRestrict_surjective
  let : IsCyclic m.range :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ m.range hp).1
  have hker (s : S) : m.rangeRestrict s = 1 ↔ j s ∈ J := by
    rw [← Subtype.val_inj]
    change e (qJ (j s)) = 1 ↔ j s ∈ J
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff _
  have hsquare (s : S) (hs : s ^ 2 = 1) : (f s) ^ 2 = 1 := by
    rw [← map_pow, hs, map_one]
  have hcomm (s t : S) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) :
      Commute (f s) (f t) := by
    by_cases hsJ : j s ∈ J
    · exact d.fixed_join_commute_mod_derived h (j s) (j t)
        (hcore s ⟨mem_map_of_mem H.subtype hsJ, s.property⟩
          (congrArg S.subtype hs)) (d.chosen_centralizer_le_sylow h t.property)
    by_cases htJ : j t ∈ J
    · exact (d.fixed_join_commute_mod_derived h (j t) (j s)
        (hcore t ⟨mem_map_of_mem H.subtype htJ, t.property⟩
          (congrArg S.subtype ht)) (d.chosen_centralizer_le_sylow h s.property)).symm
    have hmorder (u : S) (hu : u ^ 2 = 1) (huJ : j u ∉ J) :
        orderOf (m.rangeRestrict u) = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow, hu, map_one]
      · exact fun he => huJ ((hker u).mp he)
    have hmeq := IsCyclic.eq_of_orderOf_eq_two (hmorder s hs hsJ) (hmorder t ht htJ)
    have hstJ : j (s * t) ∈ J := (hker _).mp (by
      rw [map_mul, hmeq, ← pow_two, ← map_pow, ht, map_one])
    let u : J := ⟨j (s * t), hstJ⟩
    let : IsElementaryAbelian 2 (J ⧸ commutator J) :=
      (parrott_core_abelianization_structure z h).1
    have hu2 : u ^ 2 ∈ commutator J := (QuotientGroup.eq_one_iff _).mp (by
      change (QuotientGroup.mk' (commutator J)) (u ^ 2) = 1
      rw [map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (J ⧸ commutator J)) _)
    have hst2 : (f s * f t) ^ 2 = 1 := by
      rw [← map_mul, ← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact mem_map_of_mem J.subtype hu2
    exact commute_of_three_squares _ _ (hsquare s hs) (hsquare t ht) hst2
  have hcommOmega (s : S) (hs : s ∈ omega₁ S (p := 2))
      (t : S) (ht : t ∈ omega₁ S (p := 2)) : Commute (f s) (f t) := by
    refine closure_induction (p := fun s _ => Commute (f s) (f t)) ?_ ?_ ?_ ?_ hs
    · intro s hs
      refine closure_induction (p := fun t _ => Commute (f s) (f t)) ?_ ?_ ?_ ?_ ht
      · intro t ht
        exact hcomm s t hs ht
      · simpa only [map_one] using Commute.one_right (f s)
      · intro u v _ _ hu hv
        simpa only [map_mul] using hu.mul_right hv
      · intro u _ hu
        simpa only [map_inv] using hu.inv_right
    · simpa only [map_one] using Commute.one_left (f t)
    · intro u v _ _ hu hv
      simpa only [map_mul] using hu.mul_left hv
    · intro u _ hu
      simpa only [map_inv] using hu.inv_left
  apply commutator_le.mpr
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
  have hm : ⁅j s, j t⁆ ∈ D := (QuotientGroup.eq_one_iff _).mp (by
    change q ⁅j s, j t⁆ = 1
    rw [map_commutatorElement]
    exact (hcommOmega s hs t ht).commutator_eq)
  have hh := mem_map_of_mem H.subtype hm
  rw [map_map] at hh
  exact hh

/-- A core element of S outside F forces the original involution into S′. -/
private theorem omega_proper_z_mem_commutator
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    d.F < J.map H.subtype ⊓ S → z ∈ (commutator S).map S.subtype := by
  intro H J S hlt
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let B := J.map H.subtype ⊓ S
  let U := E ⊓ d.F
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  have hbound : ⁅B, U⁆ ≤ zpowers z := by
    apply commutator_le.mpr
    intro b hb e he
    obtain ⟨bH, hbJ, rfl⟩ := hb.1
    obtain ⟨eJ, heJ, rfl⟩ := he.1
    let bJ : J := ⟨bH, hbJ⟩
    have heU : eJ ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ heJ
    have hec : ⁅eJ, bJ⁆ ∈ center J := by
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp heU bJ)
    have hbc : ⁅bJ, eJ⁆ ∈ center J := by
      simpa only [commutatorElement_inv] using (center J).inv_mem hec
    rw [← hZ]
    exact ⟨⁅bJ, eJ⁆, hbc, rfl⟩
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
    exact (not_le_of_gt hlt) hBF
  have heq : ⁅B, U⁆ = zpowers z := by
    apply eq_of_le_of_card_ge hbound
    rw [Nat.card_zpowers, h.involution]
    exact (one_lt_card_iff_ne_bot _).mpr hnontrivial
  rw [map_subtype_commutator]
  apply commutator_mono (show B ≤ S from inf_le_right)
    (show U ≤ S from inf_le_right.trans d.le_chosen_centralizer)
  rw [heq]
  exact mem_zpowers z


/-- The remaining involution-coset calculation suffices for properness of
omega, using derived weak closure only in the index-two branch. -/
public theorem chosen_omega_ne_top_of_core_involutions
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hconj : IsConj z (d.a : G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (K.relIndex S = 2 → ∀ x : G, x ∈ K ⊓ S → x ^ 2 = 1 → x ∈ d.F) →
      omega₁ S (p := 2) ≠ ⊤ := by
  intro H J K S hinvol htop
  rcases d.chosen_core_relIndex_cases h with hi | hi
  · have hcard : Nat.card (K ⊓ S : Subgroup G) = 64 :=
      (d.chosen_card_of_core_relIndex_two h hi).1
    have hlt : d.F < K ⊓ S := by
      apply lt_of_le_of_ne (le_inf d.le_core d.le_chosen_centralizer)
      intro heq
      have hh := congrArg (fun L : Subgroup G => Nat.card L) heq
      rw [d.card, hcard] at hh
      omega
    have hz := d.omega_proper_z_mem_commutator h hlt
    have hle := d.chosen_omega_commutator_le_derived_of_core_involutions h (hinvol hi)
    change ⁅(omega₁ S (p := 2)).map S.subtype,
      (omega₁ S (p := 2)).map S.subtype⁆ ≤ _ at hle
    rw [htop, ← MonoidHom.range_eq_map, S.range_subtype, ← map_subtype_commutator] at hle
    exact d.chosen_characteristic_not_le_derived h hconj hderived
      (commutator S) inferInstance hz hle
  · exact d.chosen_omega_ne_top_of_core_relIndex_four h hi htop

set_option linter.unusedVariables false in
/-- The actual chosen omega is proper under the center-order-eight hypotheses.
The supplied elementary subgroup, involution and Sylow are preserved. The local
involution containment makes the extra global and center hypotheses unnecessary
for this step; they are retained for the final filtration's interface. -/
public theorem chosen_omega_ne_top_of_center_card_eight [IsSimpleGroup G]
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
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    omega₁ S (p := 2) ≠ ⊤ := by
  exact d.chosen_omega_ne_top_of_core_involutions h hconj hderived
    (d.chosen_core_centralizer_involutions_mem_fixed_join_of_relIndex_two h)

end Stellmacher.Recognition.ParrottSecondElementaryData
