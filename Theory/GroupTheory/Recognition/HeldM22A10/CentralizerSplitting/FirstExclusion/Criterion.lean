module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.Pattern
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FusionConstraints
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# The ambient contradiction for the first nonsplit centralizer pattern

An order-four root outside a binary character kernel is conjugated into the
chosen Sylow subgroup within the actual involution centralizer. Order-four
transfer then gives an ambient conjugate in the kernel. If its square is the
original involution, the conjugating element lies in its centralizer, which
contradicts character invariance. Otherwise the common centralizer has order
64. Its automorphisms fix the original involution, forcing its ambient
normalizer into the involution centralizer. The two-group normalizer condition
contradicts fusion with the central Sylow involution, whose Sylow centralizer
has order 128.

`false_of_equiv_pattern` transports the intrinsic facts from any actual group
model. Construction of those facts for `NonsplitModels.First` remains a
separate finite verification. No splitting or recognition theorem is used.

Source problem: Huppert--Blackburn III, XII.1.18(b), p.314, citing Held,
J. Algebra 8 (1968), 436--449, DOI 10.1016/0021-8693(68)90054-9. The argument
here uses the independently proved transfer and normalizer theorems imported
above; it does not claim to transcribe the unavailable original Held proof.
-/

namespace Theory.GroupTheory.HeldM22A10.FirstExclusion
open Subgroup

private theorem normalizer_map_fixed {G : Type*} [Group G]
    (H : Subgroup G) (E : Subgroup H) (z : E)
    (hfix : ∀ a : MulAut E, a z = z) :
    normalizer (E.map H.subtype : Set G) ≤ centralizer ({((z : H) : G)} : Set G) := by
  let K := E.map H.subtype
  let e : E ≃* K := E.equivMapOfInjective H.subtype H.subtype_injective
  intro g hg
  let a : MulAut K := K.normalizerMonoidHom ⟨g, hg⟩
  have hf := hfix ((e.trans a).trans e.symm)
  have he := congrArg (fun w : E => ((e w : K) : G)) hf
  simp only [MulEquiv.trans_apply, e.apply_symm_apply] at he
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  exact he

private theorem order_four_of_square {H : Type*} [Group H]
    (x z : H) (hx : x ^ 2 = z) (hz : z ^ 2 = 1) (hz1 : z ≠ 1) : orderOf x = 4 := by
  have h4 : x ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hx, hz]
  have hd := orderOf_dvd_of_pow_eq_one h4
  have hd2 : ¬ orderOf x ∣ 2 := by
    intro h
    exact hz1 (hx.symm.trans (orderOf_dvd_iff_pow_eq_one.mp h))
  have hpos : 0 < orderOf x := Nat.pos_of_dvd_of_pos hd (by decide)
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  interval_cases orderOf x <;> omega

/-- The ambient argument for a binary character and its small square-centralizers.
The local character is defined on the actual centralizer, so fusion preserving
the square of the distinguished root is conjugation inside that centralizer. -/
public theorem false_of_character {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (χ : D.centralizer →* Binary)
    (hinv : ∀ w : D.centralizer, w ^ 2 = 1 → χ w = 1)
    (x : D.centralizer) (hxsq : x ^ 2 = D.centralInvolution) (hxχ : χ x ≠ 1)
    (hC : ∀ w : D.centralizer, χ w = 1 → w ^ 2 ≠ 1 → w ^ 4 = 1 →
      w ^ 2 ≠ D.centralInvolution →
      Nat.card (centralizer ({w ^ 2} : Set D.centralizer)) = 64 ∧
      ∀ z : centralizer ({w ^ 2} : Set D.centralizer),
        (z : D.centralizer) = D.centralInvolution →
        ∀ a : MulAut (centralizer ({w ^ 2} : Set D.centralizer)),
          (a z : D.centralizer) = D.centralInvolution) : False := by
  have hzsq : D.centralInvolution ^ 2 = 1 := by
    apply Subtype.ext
    exact D.z_order ▸ pow_orderOf_eq_one D.z
  have hzne : D.centralInvolution ≠ 1 := fun h => D.z_ne_one (congrArg Subtype.val h)
  have hx4 := order_four_of_square x D.centralInvolution hxsq hzsq hzne
  have hxp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hx4]
    decide)
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq D.centralizer Q D.localSylow
  let y := (MulAut.conj a) x
  have hyS : y ∈ D.localSylow := by
    rw [← ha]
    exact Set.smul_mem_smul_set (hQ (mem_zpowers x))
  have hyχ : χ y = χ x := by
    simp [y, MulAut.conj_apply, map_mul, mul_comm]
  have hysq : y ^ 2 = D.centralInvolution := by
    rw [← map_pow, hxsq]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_center_iff.mp D.centralInvolution_mem_center a)
  let t : D.sylow := ⟨(y : G), hyS⟩
  let ι : D.sylow →* D.centralizer := inclusion D.sylow_le_centralizer
  let ψ : D.sylow →* Binary := χ.comp ι
  have ht4 : orderOf t = 4 := by
    rw [← orderOf_coe, show (t : G) = (y : G) from rfl, orderOf_coe]
    exact order_four_of_square y D.centralInvolution hysq hzsq hzne
  have hψinv : ∀ v : D.sylow, v ^ 2 = 1 → ψ v = 1 := by
    intro v hv
    apply hinv
    rw [← map_pow, hv, map_one]
  have hbinary : Nat.card Binary = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  obtain ⟨u, htu, huψ⟩ := D.order_four_conjugate_mem_character_kernel ψ hbinary hψinv t ht4
  let w := ι u
  have hwχ : χ w = 1 := huψ
  obtain ⟨g, hg⟩ := isConj_iff.mp htu
  have hg' : (MulAut.conj g) (y : G) = (w : G) := hg
  have hwsqconj : (MulAut.conj g) D.z = ((w : G) ^ 2) := by
    have hp := congrArg (fun q : G => q ^ 2) hg'
    rw [← map_pow, ← Subgroup.coe_pow, hysq] at hp
    exact hp
  have hw4 : orderOf w = 4 := by
    rw [← orderOf_coe, ← hg', MulEquiv.orderOf_eq, orderOf_coe]
    exact order_four_of_square y D.centralInvolution hysq hzsq hzne
  have hwp4 : w ^ 4 = 1 := hw4 ▸ pow_orderOf_eq_one w
  have hwp2 : w ^ 2 ≠ 1 := by
    intro hw
    have hd := orderOf_dvd_of_pow_eq_one hw
    norm_num [hw4] at hd
  by_cases hsame : w ^ 2 = D.centralInvolution
  · have hgH : g ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      simpa only [← Subgroup.coe_pow, hsame, LocalData.centralInvolution,
        MulAut.conj_apply] using hwsqconj
    have hlocal : (⟨g, hgH⟩ : D.centralizer) * y * (⟨g, hgH⟩ : D.centralizer)⁻¹ = w :=
      Subtype.ext hg'
    have hχ := congrArg χ hlocal
    simp only [map_mul, map_inv] at hχ
    have hχ' : χ y = χ w := by simpa [mul_comm, mul_left_comm] using hχ
    exact hxχ (hyχ.symm.trans (hχ'.trans hwχ))
  · obtain ⟨hcard, hfixed⟩ := hC w hwχ hwp2 hwp4 hsame
    let E := centralizer ({w ^ 2} : Set D.centralizer)
    let K := E.map D.centralizer.subtype
    have hK : K = D.centralizer ⊓ centralizer ({((w : G) ^ 2)} : Set G) := by
      exact map_subtype_centralizer_singleton D.centralizer (w ^ 2)
    have hKcard : Nat.card K = 64 :=
      (card_map_of_injective D.centralizer.subtype_injective).trans hcard
    have hKp : IsPGroup 2 K := IsPGroup.of_card (n := 6) hKcard
    have hjE : D.centralInvolution ∈ E := mem_centralizer_singleton_iff.mpr
      (mem_center_iff.mp D.centralInvolution_mem_center (w ^ 2)).symm
    let jE : E := ⟨D.centralInvolution, hjE⟩
    have hfix : ∀ f : MulAut E, f jE = jE := by
      intro f
      exact Subtype.ext (hfixed jE rfl f)
    have hN : normalizer (K : Set G) ≤ D.centralizer :=
      normalizer_map_fixed D.centralizer E jE hfix
    have hsmall : Nat.card K < Nat.card D.localSylow := by
      rw [hKcard, D.localSylow.card_eq_multiplicity, D.centralizer_card]
      decide +kernel
    have hnconj := not_isConj_of_small_common_centralizer_normalizer D.z ((w : G) ^ 2)
      (hK ▸ hKp) D.localSylow (hK ▸ hsmall)
      (by
        change normalizer ((D.centralizer ⊓ centralizer ({((w : G) ^ 2)} : Set G) :
          Subgroup G) : Set G) ≤ D.centralizer
        rw [← hK]
        exact hN)
    exact hnconj (isConj_iff.mpr ⟨g, hwsqconj⟩)

private def centralizerEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (x : H) (y : K) (hxy : e x = y) :
    centralizer ({x} : Set H) ≃* centralizer ({y} : Set K) where
  toFun z := ⟨e z, mem_centralizer_singleton_iff.mpr (by
    rw [← hxy, ← map_mul, ← map_mul]
    exact congrArg e (mem_centralizer_singleton_iff.mp z.property))⟩
  invFun z := ⟨e.symm z, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply, hxy] using
      mem_centralizer_singleton_iff.mp z.property)⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z)
  right_inv z := Subtype.ext (e.apply_symm_apply z)
  map_mul' z w := Subtype.ext (map_mul e (z : H) (w : H))

/-- The intrinsic pattern excludes any model isomorphic to the actual
involution centralizer. This theorem includes the arbitrary-universe transport
and does not require a chosen model Sylow subgroup. -/
public theorem false_of_equiv_pattern {G H : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] [Group H] (D : LocalData G) (P : Pattern H)
    (e : D.centralizer ≃* H) : False := by
  have hjne : D.centralInvolution ≠ 1 := fun h => D.z_ne_one (congrArg Subtype.val h)
  have hjC : e D.centralInvolution ∈ center H := by
    apply mem_center_iff.mpr
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa only [map_mul] using congrArg e (mem_center_iff.mp D.centralInvolution_mem_center v)
  have hj : e D.centralInvolution = P.mark := by
    rcases P.center_cases _ hjC with hone | heq
    · exact (hjne (e.injective (hone.trans e.map_one.symm))).elim
    · exact heq
  let χ : D.centralizer →* Binary := P.character.comp e.toMonoidHom
  apply false_of_character D χ
    (fun w hw => P.kills_involutions (e w) (by rw [← map_pow, hw, map_one]))
    (e.symm P.root)
  · apply e.injective
    rw [map_pow, e.apply_symm_apply, P.root_sq, hj]
  · simpa only [χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.apply_symm_apply] using P.root_character
  · intro w hwχ hw2 hw4 hwj
    have h2 : (e w) ^ 2 ≠ 1 := by
      intro he
      apply hw2
      apply e.injective
      simpa only [map_pow, map_one] using he
    have h4 : (e w) ^ 4 = 1 := by rw [← map_pow, hw4, map_one]
    have hne : (e w) ^ 2 ≠ P.mark := by
      intro he
      apply hwj
      apply e.injective
      simpa only [map_pow, hj] using he
    obtain ⟨hcard, hfixed⟩ := P.square_centralizers (e w) hwχ h2 h4 hne
    let c := centralizerEquiv e (w ^ 2) ((e w) ^ 2) (map_pow e w 2)
    refine ⟨(Nat.card_congr c.toEquiv).trans hcard, ?_⟩
    intro z hz a
    let b : MulAut (centralizer ({(e w) ^ 2} : Set H)) := (c.symm.trans a).trans c
    have hcz : (c z : H) = P.mark := by
      change e (z : D.centralizer) = P.mark
      rw [hz, hj]
    have hb := hfixed (c z) hcz b
    change (c (a (c.symm (c z))) : H) = P.mark at hb
    rw [c.symm_apply_apply] at hb
    have he : e (a z : D.centralizer) = P.mark := hb
    apply e.injective
    exact he.trans hj.symm

end Theory.GroupTheory.HeldM22A10.FirstExclusion
