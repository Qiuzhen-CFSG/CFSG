module
public import Stellmacher.Recognition.Parrott.SecondCentralizerTransferSetup
public import Stellmacher.Recognition.Parrott.SecondCentralizerWeakClosure
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaElementaryQuotient

/-!
# A character of the second-centralizer local normalizer

For any first-transfer subgroup M, the normalizer of Z(W) inside M has
ambient image WQ. Its elements send z to one of the three nonidentity
points of Z(K); matching that image by Q leaves an element of C_M(z)=W.

The compatible root b lies in W and is outside F. The elementary quotient
W/F therefore supplies a binary character detecting b. Since Q centralizes
b and has order three, transfer from W to WQ retains this character's value
on b. Pullback along the literal local-normalizer embedding gives the
character needed by the second transfer. No containment C_G(v)≤N_G(F)
is assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, pp.682–683, the local calculation underlying the Grün transfer step.
-/

open Subgroup
open scoped Pointwise IsMulCommutative

private theorem character_on_cubic_join
    {G : Type*} [Group G] [Finite G] (W A : Subgroup G)
    (hAW : A ≤ normalizer (W : Set G)) (hdis : Disjoint W A)
    (hA : Nat.card A = 3) (b : W) (hb : (b : G) ∈ centralizer (A : Set G))
    (χ : W →* Multiplicative (ZMod 2)) (hχ : χ b ≠ 1) :
    ∃ φ : (W ⊔ A : Subgroup G) →* Multiplicative (ZMod 2),
      φ ⟨b, mem_sup_left b.property⟩ ≠ 1 := by
  let J := W ⊔ A
  let S := W.subgroupOf J
  let e : S ≃* W := subgroupOfEquivOfLe le_sup_left
  let ψ := χ.comp e.toMonoidHom
  let bS : S := ⟨⟨b, mem_sup_left b.property⟩, b.property⟩
  have hi : S.index = 3 := by
    have hc := S.card_mul_index
    have hJ : Nat.card J = Nat.card W * 3 :=
      (card_sup_eq_mul_of_normalizes_of_disjoint W A hAW hdis).trans (by rw [hA])
    rw [Nat.card_congr e.toEquiv, hJ] at hc
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := W)) hc
  have hrespect (n : ℕ) (other : S)
      (hconj : IsConj (((bS ^ n) : S) : J) (other : J)) :
      ψ other = ψ (bS ^ n) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hprod : (g : G) ∈ (W : Set G) * (A : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left W A hAW]
      exact g.property
    obtain ⟨w, hw, a, ha, he⟩ := hprod
    have hc : a * (b : G) ^ n * a⁻¹ = (b : G) ^ n :=
      (show Commute a (b : G) from hb a ha).pow_right n |>.mul_inv_cancel
    have heq : (⟨w, hw⟩ : W) * b ^ n * (⟨w, hw⟩ : W)⁻¹ = e other := by
      apply Subtype.ext
      have hh := congrArg J.subtype hg
      change (g : G) * (b : G) ^ n * (g : G)⁻¹ = ((other : J) : G) at hh
      rw [← he] at hh
      have he' : (w * a) * (b : G) ^ n * (w * a)⁻¹ = w * (b : G) ^ n * w⁻¹ := by
        calc
          _ = w * (a * (b : G) ^ n * a⁻¹) * w⁻¹ := by group
          _ = _ := by rw [hc]
      exact he'.symm.trans hh
    have hh := congrArg χ heq
    simp only [map_mul, map_inv, map_pow] at hh
    rw [mul_comm (χ ⟨w, hw⟩), mul_assoc, mul_inv_cancel, mul_one] at hh
    change χ (e other) = χ (e (bS ^ n))
    rw [map_pow, show e bS = b from rfl, map_pow]
    exact hh.symm
  refine ⟨ψ.transfer, ?_⟩
  have he := ψ.transfer_apply_eq_pow_of_conjugate_powers bS hrespect
  have hp : ψ bS ^ S.index = χ b := by
    rw [hi]
    have hh := pow_mod_natCard (χ b) 3
    simpa only [show ψ bS = χ b from rfl, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card, show 3 % 2 = 1 from rfl, pow_one] using hh.symm
  change ψ.transfer (bS : J) ≠ 1
  rw [he, hp]
  exact hχ

private theorem binary_character_of_elementary
    {V : Type*} [Group V] [IsElementaryAbelian 2 V] (b : V) (hb : b ≠ 1) :
    ∃ χ : V →* Multiplicative (ZMod 2), χ b ≠ 1 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2)
    (show Additive.ofMul b ≠ 0 from hb)
  exact ⟨f.toAddMonoidHom.toMultiplicativeRight, hf⟩

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The local omega-center normalizer has ambient image exactly WQ. -/
public theorem first_transfer_omega_center_normalizer_image
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let i := N.subtype.comp K.subtype
    let W := U.map i
    let ZW := (center U).map (i.comp U.subtype)
    let A := (Q : Subgroup N).map N.subtype
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ M : Subgroup C, M.Normal → M.index = 2 → M.map C.subtype ⊓ P = W →
      let j := C.subtype.comp M.subtype
      let ZM := ZW.comap j
      (normalizer (ZM : Set M)).map j = W ⊔ A := by
  intro N K U i W ZW A C P M hMn hMi hinter j ZM
  let := hMn
  let MG := M.map C.subtype
  let ZK := (center K).map i
  have hrange : j.range = MG := by
    rw [MonoidHom.range_comp, range_subtype]
  have hWM : W ≤ MG := by rw [← hinter]; exact inf_le_left
  have hZW : ZW ≤ W := by
    rw [show ZW = ((center U).map U.subtype).map i from (map_map _ _ _).symm]
    exact map_mono (map_subtype_le _)
  have hZM : ZM.map j = ZW := map_comap_eq_self (by rw [hrange]; exact hZW.trans hWM)
  have hAM : A ≤ MG := by
    have hAC : A ≤ C := by
      have hvC : v ∈ centralizer (A : Set G) := (hfix.symm ▸ mem_zpowers v).2
      exact fun a ha => mem_centralizer_singleton_iff.mpr (hvC a ha)
    have hAcard : Nat.card (A.subgroupOf C) = 3 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
      exact (card_map_of_injective N.subtype_injective).trans
        (d.normalizer_three_card h hN hproper Q)
    have hACM : A.subgroupOf C ≤ M := by
      apply relIndex_eq_one.mp
      apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 2 3 by decide)
      · simpa only [hMi] using relIndex_dvd_index_of_normal (H := M) (K := A.subgroupOf C)
      · simpa only [hAcard] using relIndex_dvd_card M (A.subgroupOf C)
    exact fun a ha => ⟨⟨a, hAC ha⟩, hACM ha, rfl⟩
  have hWZ : W ≤ normalizer (ZW : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rintro x ⟨xK, hxU, rfl⟩ t ⟨tU, htU, rfl⟩
    exact (congrArg (i.comp U.subtype) (mem_center_iff.mp htU ⟨xK, hxU⟩)).symm
  have hAZ : A ≤ normalizer (ZW : Set G) :=
    (map_subtype_le _).trans d.normalizer_core_centers_normalized.2
  have hlift (x : G) (hxM : x ∈ MG) (hxZ : x ∈ normalizer (ZW : Set G)) :
      x ∈ (normalizer (ZM : Set M)).map j := by
    obtain ⟨m, hm⟩ := show x ∈ j.range from hrange.symm ▸ hxM
    refine ⟨m, ?_, hm⟩
    apply mem_normalizer_iff.mpr
    intro t
    change j t ∈ ZW ↔ j (m * t * m⁻¹) ∈ ZW
    simpa only [map_mul, map_inv, hm] using mem_normalizer_iff.mp hxZ (j t)
  apply le_antisymm
  · rintro x ⟨m, hm, rfl⟩
    have hxM : j m ∈ MG := hrange ▸ ⟨m, rfl⟩
    have hxZ : j m ∈ normalizer (ZW : Set G) := by
      rw [← hZM]
      exact ZM.le_normalizer_map j (mem_map_of_mem j hm)
    let t := j m * z * (j m)⁻¹
    have hzZ : z ∈ ZW := d.normalizer_core_omega_inclusions.2.1 d.z_mem_normalizer_core_center
    have htZ : t ∈ ZW := (mem_normalizer_iff.mp hxZ z).mp hzZ
    have hzt : IsConj z t := isConj_iff.mpr ⟨j m, rfl⟩
    have ht1 : t ≠ 1 := by
      intro ht
      have hz1 := isConj_one_left.mp (ht ▸ hzt)
      have hh := h.involution
      simp [hz1] at hh
    have htK : t ∈ ZK := by
      by_contra htK
      obtain ⟨a, ha⟩ := d.normalizer_omega_center_fusion_in_join h hN hproper Q v hv hfix t htZ htK
      have hvt : IsConj v t := isConj_iff.mpr ⟨a, ha⟩
      exact (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.2.1
        (hzt.trans hvt.symm)
    obtain ⟨a, ha⟩ := d.normalizer_three_core_center_fusion h hN hproper Q t htK ht1
    have hdiff : (a : G)⁻¹ * j m ∈ W := by
      have hMz : MG ⊓ centralizer ({z} : Set G) = W :=
        d.first_transfer_core_center_centralizer h hN hproper Q v hv hfix
          M hMn hinter z d.z_mem_normalizer_core_center
          (by intro hz; have hh := h.involution; simp [hz] at hh)
      rw [← hMz]
      refine ⟨MG.mul_mem (MG.inv_mem (hAM a.property)) hxM, ?_⟩
      apply mem_centralizer_singleton_iff.mpr
      have hh : (a : G) * z * (a : G)⁻¹ = j m * z * (j m)⁻¹ := ha
      have he : ((a : G)⁻¹ * j m) * z * ((a : G)⁻¹ * j m)⁻¹ = z := by
        calc
          _ = (a : G)⁻¹ * (j m * z * (j m)⁻¹) * (a : G) := by group
          _ = z := by rw [← hh]; group
      exact mul_inv_eq_iff_eq_mul.mp he
    have hm' := (W ⊔ A).mul_mem (mem_sup_right a.property) (mem_sup_left hdiff)
    simpa only [mul_inv_cancel_left] using hm'
  · exact sup_le (fun x hx => hlift x (hWM hx) (hWZ hx))
      (fun x hx => hlift x (hAM hx) (hAZ hx))

/-- The local normalizer character detecting every compatible fixed root. -/
public theorem second_centralizer_normalizer_character
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X0 := K.map N.subtype
    let D := (commutator X0).map X0.subtype
    let A := (Q : Subgroup N).map N.subtype
    X0 ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let U := omega₁ K (p := 2)
    let W := U.map (N.subtype.comp K.subtype)
    let ZW := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ M : Subgroup C, M.Normal → M.index = 2 → M.map C.subtype ⊓ P = W →
      ∀ b ∈ X0, orderOf b = 4 → b ^ 2 = v →
        X0 ⊓ centralizer (A : Set G) = zpowers b →
        let j := C.subtype.comp M.subtype
        let ZM := ZW.comap j
        ∃ φ : normalizer (ZM : Set M) →* Multiplicative (ZMod 2),
          ∀ x : normalizer (ZM : Set M), j x = b → φ x ≠ 1 := by
  intro N K X0 D A hCD v hv hfix U W ZW C P M hMn hMi hinter b hbX hb4 hb2 hbgen j ZM
  have hbW : b ∈ W := d.normalizer_fixed_root_mem_omega h hN hproper Q v hv hfix b hbX hb2
  have hbA : b ∈ centralizer (A : Set G) := (hbgen.symm ▸ mem_zpowers b).2
  have hbF : b ∉ d.F := by
    intro hb
    let : IsElementaryAbelian 2 d.F := d.elementary
    have hd := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb)
    rw [hb4] at hd
    norm_num at hd
  have hWN : W ≤ N := by
    rintro x ⟨k, _, rfl⟩
    exact k.val.property
  have hNW : N ≤ normalizer (W : Set G) := by
    let B := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : B.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map (H := B) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, B, W, map_map] using hh
  let F₀ := d.F.subgroupOf W
  let : F₀.Normal := normal_subgroupOf_of_le_normalizer hWN
  let V := W ⧸ F₀
  let f := QuotientGroup.mk' F₀
  have hsq (x : V) : x ^ 2 = 1 := by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective F₀ x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (d.normalizer_omega_square_mem_elementary h hN hproper Q hCD w w.property)
  have hcomm : IsMulCommutative V := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hinv (t : V) : t⁻¹ = t :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq t)
    calc
      x * y = (x * y)⁻¹ := (hinv _).symm
      _ = y * x := by rw [mul_inv_rev, hinv, hinv]
  let : IsElementaryAbelian 2 V := {
    toIsMulCommutative := hcomm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  let bW : W := ⟨b, hbW⟩
  obtain ⟨χ₀, hχ₀⟩ := binary_character_of_elementary (f bW)
    (fun he => hbF ((QuotientGroup.eq_one_iff bW).mp he))
  let χ := χ₀.comp f
  have hχ : χ bW ≠ 1 := hχ₀
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans (d.normalizer_three_card h hN hproper Q)
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective (f := N.subtype.comp K.subtype)
      (K := U) (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).1
  have hdis : Disjoint W A := disjoint_of_coprime_natCard (by rw [hWcard, hAcard]; decide)
  obtain ⟨φ, hφ⟩ := character_on_cubic_join W A ((map_subtype_le _).trans hNW)
    hdis hAcard bW hbA χ hχ
  have hmap : (normalizer (ZM : Set M)).map j = W ⊔ A :=
    d.first_transfer_omega_center_normalizer_image h hN hproper Q v hv hfix M hMn hMi hinter
  let g : normalizer (ZM : Set M) →* (W ⊔ A : Subgroup G) := {
    toFun x := ⟨j x, hmap ▸ mem_map_of_mem j x.property⟩
    map_one' := Subtype.ext (map_one j)
    map_mul' x y := Subtype.ext (map_mul j (x : M) (y : M)) }
  refine ⟨φ.comp g, ?_⟩
  intro x hx
  have he : g x = ⟨bW, mem_sup_left bW.property⟩ := Subtype.ext hx
  change φ (g x) ≠ 1
  rw [he]
  exact hφ

end Stellmacher.Recognition.ParrottSecondElementaryData
