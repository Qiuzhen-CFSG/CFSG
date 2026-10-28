module

public import Theory.GroupTheory.PGroup.NormalEightNormLifting
public import Theory.GroupTheory.PGroup.NormalFourCentralAction

/-!
# Norm control above a normal omega four

A normal commuting action subgroup with binary inverted elements and surjective
binary norms has no involutions outside a self-centralizing abelian base, provided
it centralizes the base's normal omega four and the ambient group has no normal
elementary eight. The whole ambient group need not centralize that four.

Norm correction closes involution cosets. A nontrivial normal image in the
quotient by the base meets the center, and its involution lift gives a normal
elementary eight. This adapts the central-four argument in
`NormalEightNormLifting` to a normal four using `NormalFourCentralAction`.

Source: MacWilliams, Trans. AMS 150 (1970), §1.2; Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.1, printed p.385.
-/

open Subgroup

namespace NormalFourNormControl

/-- A normal subgroup with binary-inverting involution representatives
centralizing the normal omega four is contained in the abelian base. -/
public theorem normal_le_of_involution_cosets_with_binary_inversions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (N : Subgroup P) [N.Normal]
    (hlift : ∀ x ∈ N, ∃ a : P, a ^ 2 = 1 ∧ x * a⁻¹ ∈ D ∧
      a ∈ centralizer (W : Set P) ∧
      ∀ d ∈ D, a * d * a⁻¹ = d⁻¹ → d ^ 2 = 1) : N ≤ D := by
  classical
  by_contra hND
  let q := QuotientGroup.mk' D
  let B := N.map q
  let : B.Normal := inferInstance
  have hBne : B ≠ ⊥ := by
    intro h
    apply hND
    simpa [q] using (map_eq_bot_iff (f := q) N).mp h
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hBne
  let : Fact (IsPGroup 2 (P ⧸ D)) := ⟨hP.to_quotient D⟩
  obtain ⟨b, hbne, hbcenter⟩ := exists_nontrivial_center_mem_normal B (p := 2)
  obtain ⟨x, hx, hxb⟩ := b.property
  obtain ⟨a, ha, hxa, hfix, hinv⟩ := hlift x hx
  have hqa : q a = q x := by
    have he : q (x * a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hxa
    exact (mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using he)).symm
  have haD : a ∈ D := by
    by_contra haD
    apply hno
    apply exists_normal_eight_of_involution_central_action W D hW hD hO a ha haD hfix _ hinv
    intro g
    have hd : g * a * g⁻¹ * a⁻¹ ∈ D := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (g * a * g⁻¹ * a⁻¹) = 1
      simp only [map_mul, map_inv, hqa, hxb]
      rw [mem_center_iff.mp hbcenter (q g), mul_inv_cancel_right, mul_inv_cancel]
    have hc : MulAut.conjNormal (H := D) (g * a * g⁻¹ * a⁻¹) = 1 := by
      ext d
      change (g * a * g⁻¹ * a⁻¹) * (d : P) * (g * a * g⁻¹ * a⁻¹)⁻¹ = d
      rw [← D.le_centralizer hd d d.property, mul_inv_cancel_right]
    simp only [map_mul, map_inv] at hc
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)
  apply hbne
  apply Subtype.ext
  exact hxb.symm.trans (hqa.symm.trans ((QuotientGroup.eq_one_iff _).mpr haD))

/-- Norm correction closes the involution cosets in a commuting action subgroup. -/
private theorem norm_correct_product
    {P : Type*} [Group P]
    (D K : Subgroup P) [D.Normal] (hDK : D ≤ K)
    (hD : centralizer (D : Set P) ≤ D)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K,
      Commute (MulAut.conjNormal (H := D) a) (MulAut.conjNormal b))
    (hinv : ∀ a ∈ K, ∀ d ∈ D, a * d * a⁻¹ = d⁻¹ → d ^ 2 = 1)
    (hnorm : ∀ a ∈ K, ∀ d : D, d ^ 2 = 1 →
      ∃ t : D, t * MulAut.conjNormal a t = d)
    {a b : P} (haK : a ∈ K) (ha : a ^ 2 = 1)
    (hbK : b ∈ K) (hb : b ^ 2 = 1) :
    ∃ c ∈ K, c ^ 2 = 1 ∧
      QuotientGroup.mk' D c = QuotientGroup.mk' D a * QuotientGroup.mk' D b := by
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have hc : MulAut.conjNormal (H := D) ((a * b) ^ 2) = 1 := by
    have he : (a * b) ^ 2 = a * b * a⁻¹ * b⁻¹ := by simp only [hai, hbi, pow_two, mul_assoc]
    rw [he, map_mul, map_mul, map_mul, map_inv, map_inv,
      (hcomm a haK b hbK).eq, mul_inv_cancel_right, mul_inv_cancel]
  have hsD : (a * b) ^ 2 ∈ D := by
    apply hD
    intro d hd
    have he := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P)) hc
    change (a * b) ^ 2 * d * ((a * b) ^ 2)⁻¹ = d at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hs : ((a * b) ^ 2) ^ 2 = 1 := by
    apply hinv a haK _ hsD
    simp only [pow_two, mul_inv_rev, hai, hbi]
    simp only [← mul_assoc, haa, one_mul]
  let d : D := ⟨((a * b) ^ 2)⁻¹, D.inv_mem hsD⟩
  have hd : d ^ 2 = 1 := by
    apply Subtype.ext
    change (((a * b) ^ 2)⁻¹) ^ 2 = 1
    rw [inv_pow, hs, inv_one]
  obtain ⟨t, ht⟩ := hnorm (a * b) (K.mul_mem haK hbK) d hd
  refine ⟨(t : P) * (a * b), K.mul_mem (hDK t.property) (K.mul_mem haK hbK), ?_, ?_⟩
  · have htP : (t : P) * ((a * b) * (t : P) * (a * b)⁻¹) = ((a * b) ^ 2)⁻¹ :=
      congrArg Subtype.val ht
    calc
      ((t : P) * (a * b)) ^ 2 =
          ((t : P) * ((a * b) * (t : P) * (a * b)⁻¹)) * (a * b) ^ 2 := by
            simp only [pow_two]; group
      _ = 1 := by rw [htP, inv_mul_cancel]
  · have htq : QuotientGroup.mk' D (t : P) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr t.property
    simp only [map_mul, htq, one_mul]

/-- A normal commuting action subgroup with binary inverted elements and
surjective binary norm maps contains no involutions outside `D`. -/
public theorem involution_mem_of_normal_norm_control
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (K : Subgroup P) [K.Normal] (hDK : D ≤ K)
    (hfix : K ≤ centralizer (W : Set P))
    (hcomm : ∀ a ∈ K, ∀ b ∈ K,
      Commute (MulAut.conjNormal (H := D) a) (MulAut.conjNormal b))
    (hinv : ∀ a ∈ K, ∀ d ∈ D, a * d * a⁻¹ = d⁻¹ → d ^ 2 = 1)
    (hnorm : ∀ a ∈ K, ∀ d : D, d ^ 2 = 1 →
      ∃ t : D, t * MulAut.conjNormal a t = d)
    (a : P) (haK : a ∈ K) (ha : a ^ 2 = 1) : a ∈ D := by
  let q := QuotientGroup.mk' D
  let O := omega₁ K (p := 2)
  let : O.Characteristic := omega₁_characteristic K
  let N := O.map K.subtype
  let : N.Normal := ConjAct.normal_of_characteristic_of_normal
  have hlift : ∀ y ∈ O, ∃ b ∈ K, b ^ 2 = 1 ∧ q (y : P) = q b := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact ⟨y, y.property, congrArg Subtype.val hy, rfl⟩
    | one => exact ⟨1, K.one_mem, by simp, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨b, hbK, hb, hyb⟩ := hy
      obtain ⟨c, hcK, hc, hzc⟩ := hz
      obtain ⟨d, hdK, hd, hqd⟩ := norm_correct_product D K hDK hD hcomm hinv hnorm hbK hb hcK hc
      refine ⟨d, hdK, hd, ?_⟩
      change q ((y : P) * (z : P)) = q d
      rw [map_mul, hyb, hzc]
      exact hqd.symm
    | inv y _ hy =>
      obtain ⟨b, hbK, hb, hyb⟩ := hy
      refine ⟨b⁻¹, K.inv_mem hbK, by rw [inv_pow, hb, inv_one], ?_⟩
      change q (y : P)⁻¹ = q b⁻¹
      rw [map_inv, map_inv, hyb]
  have hND : N ≤ D := by
    apply normal_le_of_involution_cosets_with_binary_inversions hP hno W hW D hD hO N
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨b, hbK, hb, hyb⟩ := hlift y hy
    refine ⟨b, hb, (QuotientGroup.eq_one_iff _).mp ?_, hfix hbK, hinv b hbK⟩
    change q ((y : P) * b⁻¹) = 1
    rw [map_mul, map_inv, hyb, mul_inv_cancel]
  apply hND
  exact ⟨⟨a, haK⟩, subset_closure (show (⟨a, haK⟩ : K) ^ (2^1) = 1 from
    Subtype.ext ha), rfl⟩


/-- An elementary conjugation image avoids every norm-control subgroup.
The statement is transported to any chosen model of the abelian subgroup. -/
public theorem conj_image_disjoint_norm_control
    {P V : Type*} [Group P] [Finite P] [Group V] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* V) (T : InvolutionNormControl V) [T.subgroup.Normal]
    (hTfix : ∀ f ∈ T.subgroup, ∀ x : V, x ^ 2 = 1 → f x = x)
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    (((MulAut.congr e).toMonoidHom.comp
      ((MulAut.conjNormal : P →* MulAut D).comp A.subtype)).range) ⊓ T.subgroup = ⊥ := by
  let c : P →* MulAut D := MulAut.conjNormal
  let F : P →* MulAut V := (MulAut.congr e).toMonoidHom.comp c
  let K := T.subgroup.comap F
  let : K.Normal := ⟨by
    intro x hx g
    change F (g * x * g⁻¹) ∈ T.subgroup
    rw [map_mul, map_mul, map_inv]
    exact (inferInstance : T.subgroup.Normal).conj_mem (F x) hx (F g)⟩
  have htriv (d : P) (hd : d ∈ D) : c d = 1 := by
    ext x
    change d * (x : P) * d⁻¹ = x
    rw [← D.le_centralizer hd x x.property, mul_inv_cancel_right]
  have hDK : D ≤ K := by
    intro d hd
    change (MulAut.congr e) (c d) ∈ T.subgroup
    rw [htriv d hd, map_one]
    exact T.subgroup.one_mem
  have hKfix : K ≤ centralizer (W : Set P) := by
    intro a ha w hw
    have hwD : w ∈ D := (hO ▸ map_subtype_le _) hw
    let d : D := ⟨w, hwD⟩
    have hd : d ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw)
    have he := hTfix (F a) ha (e d) (by rw [← map_pow, hd, map_one])
    change e (c a (e.symm (e d))) = e d at he
    rw [e.symm_apply_apply] at he
    have hh := congrArg Subtype.val (e.injective he)
    change a * w * a⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcomm (a : P) (ha : a ∈ K) (b : P) (hb : b ∈ K) :
      Commute (c a) (c b) := by
    apply Commute.of_map (MulAut.congr e).injective
    exact T.commute (F a) ha (F b) hb
  have hinv (a : P) (ha : a ∈ K) (d : P) (hd : d ∈ D)
      (he : a * d * a⁻¹ = d⁻¹) : d ^ 2 = 1 := by
    let d' : D := ⟨d, hd⟩
    have he' : F a (e d') = (e d')⁻¹ := by
      change e (c a (e.symm (e d'))) = (e d')⁻¹
      rw [e.symm_apply_apply, ← map_inv]
      exact congrArg e (Subtype.ext he)
    have hs := T.inverted (F a) ha (e d') he'
    have hs' : d' ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using hs)
    exact congrArg Subtype.val hs'
  have hnorm (a : P) (ha : a ∈ K) (d : D) (hd : d ^ 2 = 1) :
      ∃ t : D, t * c a t = d := by
    obtain ⟨y, hy⟩ := T.norm (F a) ha (e d) (by rw [← map_pow, hd, map_one])
    refine ⟨e.symm y, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply]
    exact hy
  apply eq_bot_iff.mpr
  rintro f ⟨⟨a, rfl⟩, haT⟩
  have haK : (a : P) ∈ K := haT
  have haD := involution_mem_of_normal_norm_control hP hno W hW D hD hO K hDK
    hKfix hcomm hinv hnorm a haK (elemPow_eq_one_of_isElementaryAbelian (a : P) a.property)
  change (MulAut.congr e) (c a) = 1
  rw [htriv a haD, map_one]


end NormalFourNormControl
