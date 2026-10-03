module

public import Stellmacher.Recognition.Parrott.NormalizerCoreCenter
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaLocal
public import Stellmacher.Recognition.Parrott.DerivedTCoreInvolutions
public import Stellmacher.Recognition.Parrott.DerivedTCentralizerCore
public import Stellmacher.Recognition.Parrott.ElementaryJoin
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The omega subgroup of the second normalizer core

For the supplied F and T, put N=N_G(F), K=O₂(N), and U=Ω₁(K).
The equality K=C_T(t) puts the elementary derived core E in K, hence
in U. Together with F≤U and C_G(E)=E this places the ambient center
of U in E∩F. The join is strictly smaller than U: otherwise its derived
line ⟨z⟩ is normal in N, contradicting T<N. This supplies a core involution
outside E∨F and excludes center order sixteen. The cyclic order-four image
of K in H/J also makes U proper. Thus 128≤|U|≤512 and 4≤|Z(U)|≤8.
Core involutions centralizing t lie in E∨F, so the witness outside that join
lies outside the original core J. The local fixed-space calculation then gives
|U|=256, |Z(U)|=8, and U=C_K(Z(U)). All embeddings below are the actual subgroup
inclusions.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the structure calculations surrounding Lemma 6.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The actual omega subgroup contains both elementary subgroups. -/
public theorem elementary_join_le_normalizer_core_omega (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    E ⊔ d.F ≤ (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) := by
  intro H J E N K
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator h hN hproper
  have htZ : t ∈ (center K).map (N.subtype.comp K.subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hEK : E ≤ K.map N.subtype := by
    rw [d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz]
    exact d.derived_le_t_centralizer h t ht.1
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  refine sup_le ?_ d.normalizer_core_omega_inclusions.1
  intro e he
  obtain ⟨eN, heK, heq⟩ := hEK he
  let eK : K := ⟨eN, heK⟩
  have heU : eK ∈ omega₁ K (p := 2) := by
    apply Subgroup.subset_closure
    apply Subtype.ext
    apply Subtype.ext
    change (eN : G) ^ (2 ^ 1) = 1
    change (eN : G) = e at heq
    rw [heq]
    exact elemPow_eq_one_of_isElementaryAbelian e he
  exact ⟨eK, heU, heq⟩

/-- The ambient center of the actual omega subgroup lies in E∩F. -/
public theorem normalizer_core_omega_center_le_inf (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let embed := N.subtype.comp K.subtype
    (center U).map (embed.comp U.subtype) ≤ E ⊓ d.F := by
  intro H J E N K U embed
  refine le_inf ?_ d.normalizer_core_omega_inclusions.2.2
  have hEU : E ≤ U.map embed :=
    le_sup_left.trans (d.elementary_join_le_normalizer_core_omega h hN hproper)
  rw [← show centralizer (E : Set G) = E from parrott_derived_centralizer z h]
  rintro x ⟨xU, hxZ, rfl⟩ e he
  obtain ⟨eK, heU, rfl⟩ := hEU he
  exact congrArg (embed.comp U.subtype) (mem_center_iff.mp hxZ ⟨eK, heU⟩)

/-- The omega image cannot be the join of the two elementary subgroups:
its characteristic derived line would force the whole normalizer to fix z. -/
public theorem elementary_join_lt_normalizer_core_omega (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    E ⊔ d.F < (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) := by
  intro H J E N K
  let U := omega₁ K (p := 2)
  let W := U.map K.subtype
  let X := U.map (N.subtype.comp K.subtype)
  let A := E ⊔ d.F
  have hAX : A ≤ X := d.elementary_join_le_normalizer_core_omega h hN hproper
  refine lt_of_le_of_ne hAX ?_
  intro heq
  let : U.Characteristic := omega₁_characteristic K
  let : W.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNX : N ≤ normalizer (X : Set G) := by
    have hh := le_normalizer_map (H := W) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, W, X, map_map] using hh
  have hNA : N ≤ normalizer (A : Set G) := by
    change A = X at heq
    rwa [← heq] at hNX
  have hAH : normalizer (A : Set G) ≤ H :=
    normalizer_le_centralizer_of_characteristic_involution A (commutator A)
      z h.involution (d.elementary_join_commutator h)
  have hNT : N ≤ (d.sylow : Subgroup G) := by
    rw [← d.normalizer_inf_centralizer h]
    exact le_inf le_rfl (hNA.trans hAH)
  exact hproper.not_ge hNT

omit [Finite G] in
/-- The ambient center is elementary abelian since it lies in F. -/
public theorem normalizer_core_omega_center_elementary (d : ParrottSecondElementaryData z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    IsElementaryAbelian 2 (center U) := by
  intro N K U
  let i := (N.subtype.comp K.subtype).comp U.subtype
  let Z := (center U).map i
  let : IsElementaryAbelian 2 d.F := d.elementary
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro c
  apply Subtype.ext
  apply (N.subtype_injective.comp (K.subtype_injective.comp U.subtype_injective))
  change i ((c : U) ^ 2) = i 1
  rw [map_pow, map_one]
  exact elemPow_eq_one_of_isElementaryAbelian _
    (d.normalizer_core_omega_inclusions.2.2 (mem_map_of_mem i c.property))
/-- Self-centralization of E∩F excludes order sixteen for the omega center. -/
public theorem normalizer_core_omega_center_card_bounds (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    4 ≤ Nat.card (center U) ∧ Nat.card (center U) ≤ 8 := by
  intro N K U
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let i := N.subtype.comp K.subtype
  let X := U.map i
  let Z := (center U).map (i.comp U.subtype)
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hZcard : Nat.card Z = Nat.card (center U) := card_map_of_injective (hi.comp U.subtype_injective)
  have hZle : Z ≤ E ⊓ d.F := d.normalizer_core_omega_center_le_inf h hN hproper
  have hlo : 4 ≤ Nat.card Z := by
    have hh := card_le_of_le d.normalizer_core_omega_inclusions.2.1
    rw [card_map_of_injective hi, (d.normalizer_core_order h hN hproper).2.2.2] at hh
    exact hh
  have hlt : Nat.card Z < 16 := by
    have hle := (card_le_of_le hZle).trans_eq d.inf_card
    have hne : Nat.card Z ≠ 16 := by
      intro hc
      have heq : Z = E ⊓ d.F := eq_of_le_of_card_ge hZle (by rw [hc, d.inf_card])
      have hXC : X ≤ centralizer (Z : Set G) := by
        rintro x ⟨xK, hxU, rfl⟩ z ⟨zU, hzZ, rfl⟩
        exact (congrArg (i.comp U.subtype) (mem_center_iff.mp hzZ ⟨xK, hxU⟩)).symm
      rw [heq] at hXC
      have hC : centralizer (E ⊓ d.F : Set G) = E ⊔ d.F :=
        d.elementary_inf_centralizer h
      change X ≤ centralizer (E ⊓ d.F : Set G) at hXC
      rw [hC] at hXC
      exact (d.elementary_join_lt_normalizer_core_omega h hN hproper).not_ge hXC
    omega
  have hd : Nat.card Z ∣ 2 ^ 4 := by
    have hh := card_dvd_of_le hZle
    rw [d.inf_card] at hh
    exact hh
  obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rw [← hZcard]
  refine ⟨hlo, ?_⟩
  rw [hc] at hlo hlt ⊢
  interval_cases n <;> norm_num at *

/-- Strict containment of the order-64 join gives the next two-power bound. -/
public theorem normalizer_core_omega_card_lower_bound (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    128 ≤ Nat.card (omega₁ K (p := 2)) := by
  intro N K
  let U := omega₁ K (p := 2)
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let i := N.subtype.comp K.subtype
  let X := U.map i
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hXcard : Nat.card X = Nat.card U := card_map_of_injective hi
  have hAX : E ⊔ d.F < X := d.elementary_join_lt_normalizer_core_omega h hN hproper
  have hlt : 64 < Nat.card X := by
    have hle := card_le_of_le hAX.le
    rw [d.elementary_join_card h] at hle
    have hne : Nat.card X ≠ 64 := by
      intro hc
      exact hAX.ne (eq_of_le_of_card_ge hAX.le (by rw [hc, d.elementary_join_card h]))
    omega
  have hd : Nat.card U ∣ 2 ^ 10 := by
    have hh := U.card_subgroup_dvd_card
    rw [(d.normalizer_core_order h hN hproper).2.1] at hh
    exact hh
  obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rw [hXcard] at hlt
  change 128 ≤ Nat.card U
  rw [hc] at hlt ⊢
  interval_cases n <;> norm_num at *

/-- The actual omega is proper: its cyclic quotient image has exponent two,
whereas K contains an element of quotient order four. -/
public theorem normalizer_core_omega_ne_top (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    omega₁ K (p := 2) ≠ ⊤ := by
  intro N K htop
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let i := N.subtype.comp K.subtype
  let X := K.map N.subtype
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator h hN hproper
  have htZ : t ∈ (center K).map i := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hXC := d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024 := by
    rw [← hXC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order h hN hproper).2.1
  obtain ⟨y, hy, hy4⟩ := d.t_centralizer_exists_quotient_order_four h t ht.1 htz hCcard
  have hXH : X ≤ H := d.normalizer_core_le_sylow.trans d.sylow_le_centralizer
  let j : K →* H := i.codRestrict H (fun k => hXH (mem_map_of_mem N.subtype k.property))
  let q := (QuotientGroup.mk' J).comp j
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let f := e.toMonoidHom.comp q
  have hp : IsPGroup 2 f.range :=
    pCore_isPGroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : IsCyclic f.range :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ f.range hp).1
  have hsquare : ∀ k ∈ omega₁ K (p := 2), (f.rangeRestrict k) ^ 2 = 1 := by
    intro k hk
    refine closure_induction (p := fun k _ => (f.rangeRestrict k) ^ 2 = 1) ?_ ?_ ?_ ?_ hk
    · intro k hk
      change k ^ (2 ^ 1) = 1 at hk
      rw [← map_pow, show k ^ 2 = 1 from hk, map_one]
    · simp only [map_one, one_pow]
    · intro a b _ _ ha hb
      rw [map_mul, mul_pow, ha, hb, one_mul]
    · intro a _ ha
      rw [map_inv, inv_pow, ha, inv_one]
  have hyX : (y : G) ∈ X := by
    change X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) at hXC
    rwa [hXC]
  obtain ⟨yN, hyK, hyy⟩ := hyX
  let k : K := ⟨yN, hyK⟩
  have hjk : j k = y := Subtype.ext hyy
  have hk2 := hsquare k (htop ▸ mem_top k)
  have hf2 : (f k) ^ 2 = 1 := congrArg Subtype.val hk2
  have hq2 : (QuotientGroup.mk' J y) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simpa only [f, q, MonoidHom.comp_apply, hjk, MulEquiv.coe_toMonoidHom] using hf2
  have hd := orderOf_dvd_of_pow_eq_one hq2
  rw [hy4] at hd
  norm_num at hd

/-- Properness in the order-1024 core bounds the omega order by 512. -/
public theorem normalizer_core_omega_card_upper_bound (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    Nat.card (omega₁ K (p := 2)) ≤ 512 := by
  intro N K
  let U := omega₁ K (p := 2)
  have hc := U.index_mul_card
  rw [(d.normalizer_core_order h hN hproper).2.1] at hc
  have hindex : 2 ≤ U.index := by
    have hn : U.index ≠ 1 := fun he => d.normalizer_core_omega_ne_top h hN hproper (index_eq_one.mp he)
    have hz : U.index ≠ 0 := by intro he; rw [he, zero_mul] at hc; omega
    omega
  change Nat.card U ≤ 512
  nlinarith

/-- A square-one generator witnesses strict enlargement of E∨F inside Ω₁(K).
The witness already belongs to the actual normalizer core. -/
public theorem exists_normalizer_core_involution_outside_elementary_join
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ y : G, y ∈ K.map N.subtype ∧ orderOf y = 2 ∧ y ∉ E ⊔ d.F := by
  classical
  intro H J E N K
  let i := N.subtype.comp K.subtype
  by_contra hnone
  have hU : (omega₁ K (p := 2)).map i ≤ E ⊔ d.F := by
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro k hk
    change k ^ (2 ^ 1) = 1 at hk
    change i k ∈ E ⊔ d.F
    by_contra hout
    apply hnone
    refine ⟨i k, mem_map_of_mem N.subtype k.property, ?_, hout⟩
    apply orderOf_eq_prime
    · rw [← map_pow, show k ^ 2 = 1 from hk, map_one]
    · intro heq
      exact hout (heq ▸ (E ⊔ d.F).one_mem)
  exact (d.elementary_join_lt_normalizer_core_omega h hN hproper).not_ge hU

/-- The actual normalizer core contains an involution outside the original
core. In particular this establishes the required involution in T−J. -/
public theorem exists_normalizer_core_involution_outside_original_core
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ y : G, y ∈ K.map N.subtype ∧ orderOf y = 2 ∧ y ∉ J.map H.subtype := by
  intro H J N K
  obtain ⟨y, hyK, hy2, hyA⟩ :=
    d.exists_normalizer_core_involution_outside_elementary_join h hN hproper
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator h hN hproper
  have htZ : t ∈ (center K).map (N.subtype.comp K.subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hKC := d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← hKC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order h hN hproper).2.1
  refine ⟨y, hyK, hy2, ?_⟩
  intro hyJ
  have hyt : y ∈ centralizer ({t} : Set G) := (hKC ▸ hyK).2
  exact hyA (d.t_centralizer_core_involution_mem_elementary_join h t ht htz hCcard
    y ⟨hyJ, hyt⟩ (hy2 ▸ pow_orderOf_eq_one y))

/-- The actual omega has order 256 and center of order eight. Its ambient
center lies in E∩F, and its ambient image is the centralizer of that center
inside the actual normalizer core. No outer involution is assumed. -/
public theorem normalizer_core_omega_structure
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let embed := N.subtype.comp K.subtype
    let X := U.map embed
    let Z := (center U).map (embed.comp U.subtype)
    Nat.card U = 256 ∧ Nat.card (center U) = 8 ∧ Z ≤ E ⊓ d.F ∧
      X = K.map N.subtype ⊓ centralizer (Z : Set G) := by
  intro H J E N K U embed X Z
  obtain ⟨y, hyK, hy2, hyJ⟩ :=
    d.exists_normalizer_core_involution_outside_original_core h hN hproper
  obtain ⟨hU, hZ, hX⟩ :=
    d.normalizer_core_omega_structure_of_outer_involution h hN hproper y hyK hy2 hyJ
  exact ⟨hU, hZ, d.normalizer_core_omega_center_le_inf h hN hproper, hX⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
