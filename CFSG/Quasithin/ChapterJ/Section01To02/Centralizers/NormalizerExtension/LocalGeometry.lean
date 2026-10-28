module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.Quotient
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.FusionSylow
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Orders

/-!
# The local centralizer and inverter geometry in J.2.7(3)

The literal Ru2 image of S is a two-group acting on five letters, so it has
a fixed point. Earlier involution fusion makes the image of s a nonidentity
even involution, whose fixed point is unique. The parabolic image normalizes
the image of S and has order 24, so it is the full stabilizer of that point.
Thus the centralizer of the image of s lies in the original parabolic image.
Pullback gives C_H(s) ≤ L. The J.2.3 product for C_L(s) and the absence of seven
in |H| then give C_H(s) = T_s, preserving the original S, s and T_s.

For inversion, two conjugate involutions in S₅ can be chosen with product of
order three. Lift the conjugator through the given Ru2 quotient map. The
product upstairs is inverted by the supplied involution, and a suitable power
has order three. Sylow conjugacy in H transports this actual subgroup to the
original B, with the conjugator and inversion identities retained. This is
the dihedral lifting argument underlying `SymmetricThreeQuotientInverter`,
applied directly to the two generating involutions in the genuine S₅ image.

The earlier-source `SourceJ26` and the original Sylow-three witness in H
remain explicit. No normalizer recognition or control of s-fusion is assumed.
Final J.2.7(3) assembly belongs to `NormalizerExtension`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.7(3), printed p.436 (PDF p.447).
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices

private theorem perm_five_involution_product :
    ∀ t : S5, t ^ 2 = 1 → t ≠ 1 → ∃ a : Fin 5,
      let u := Equiv.swap 0 a
      (t * (u * t * u⁻¹)) ^ 3 = 1 ∧ t * (u * t * u⁻¹) ≠ 1 := by
  decide +kernel

private theorem inverted_three_in_H {G : Type*} [Group G] [Finite G]
    (d : LocalSetup G) (w : d.toTypeRuSetup.H)
    (hw : w ^ 2 = 1) (hwQ : (w : G) ∉ d.toTypeRuSetup.Q) :
    ∃ A : Subgroup d.toTypeRuSetup.H, Nat.card A = 3 ∧
      ∀ a ∈ A, w * a * w⁻¹ = a⁻¹ := by
  let f := d.ru2.quotientMap
  have hfw : f w ≠ 1 := by
    intro he
    have hk : w ∈ f.ker := he
    rw [d.ru2.quotient_kernel] at hk
    exact hwQ hk
  obtain ⟨a, ha3, hane⟩ := perm_five_involution_product (f w)
    (by rw [← map_pow, hw, map_one]) hfw
  obtain ⟨g, hg⟩ := d.ru2.quotient_surjective (Equiv.swap 0 a)
  have hg' : f g = Equiv.swap 0 a := hg
  let x := w * (g * w * g⁻¹)
  have hfx : orderOf (f x) = 3 := by
    apply orderOf_eq_prime
    · simpa only [x, map_mul, map_inv, hg'] using ha3
    · simpa only [x, map_mul, map_inv, hg'] using hane
  have hthree : 3 ∣ orderOf x := hfx ▸ orderOf_map_dvd f x
  let y := x ^ (orderOf x / 3)
  have hy : orderOf y = 3 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hthree
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hxinv : w * x * w⁻¹ = x⁻¹ := by
    calc
      w * x * w⁻¹ = w ^ 2 * (g * w * g⁻¹) * w⁻¹ := by simp only [x, pow_two, mul_assoc]
      _ = (g * w * g⁻¹) * w⁻¹ := by rw [hw, one_mul]
      _ = x⁻¹ := by simp only [x, mul_inv_rev, inv_inv, hwinv, mul_assoc]
  have hyinv : w * y * w⁻¹ = y⁻¹ := by
    change MulAut.conj w (x ^ (orderOf x / 3)) = y⁻¹
    rw [map_pow]
    change (w * x * w⁻¹) ^ (orderOf x / 3) = y⁻¹
    rw [hxinv, inv_pow]
  refine ⟨zpowers y, (Nat.card_zpowers y).trans hy, ?_⟩
  intro a ha
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
  change MulAut.conj w (y ^ n) = (y ^ n)⁻¹
  rw [map_zpow]
  change (w * y * w⁻¹) ^ n = (y ^ n)⁻¹
  rw [hyinv, inv_zpow]

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The original Sylow-three witness recovers B after constructing an actual
inverted three-subgroup in H. -/
theorem inverterTransport_source
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B) :
    c.InverterTransport := by
  intro i hiK hiQ hi2
  have hiH := d.toTypeRuSetup.K_le_H hiK
  let w : d.toTypeRuSetup.H := ⟨i, hiH⟩
  have hw : w ^ 2 = 1 := Subtype.ext (hi2 ▸ pow_orderOf_eq_one i)
  obtain ⟨A, hA, hinv⟩ := inverted_three_in_H d w hw hiQ
  obtain ⟨R, hAR⟩ := (IsPGroup.of_card (p := 3) (n := 1) hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq d.toTypeRuSetup.H R P
  let e := MulAut.conj g
  have hAP : A.map e.toMonoidHom ≤ (P : Subgroup d.toTypeRuSetup.H) := by
    rw [← hg]
    exact map_mono hAR
  have hB : Nat.card c.B = 3 :=
    SpecialCore.cubicSubgroup_card d.toTypeRuSetup c.sylowThree d.card_Z
      (d.center_eq.le.trans inf_le_left)
  have hPc : Nat.card (P : Subgroup d.toTypeRuSetup.H) = 3 := by
    have hc := congrArg (fun U : Subgroup G => Nat.card U) hP
    rw [card_map_of_injective d.toTypeRuSetup.H.subtype_injective, hB] at hc
    exact hc
  have hAPeq : A.map e.toMonoidHom = (P : Subgroup d.toTypeRuSetup.H) :=
    eq_of_le_of_card_ge hAP (by rw [card_map_of_injective e.injective, hA, hPc])
  refine ⟨g, g.property, ?_⟩
  intro b hb
  rw [← hP] at hb
  obtain ⟨bH, hbH, rfl⟩ := hb
  rw [← hAPeq] at hbH
  obtain ⟨a, ha, rfl⟩ := hbH
  have he := congrArg e (hinv a ha)
  simp only [map_mul, map_inv] at he
  have heG := congrArg (fun x : d.toTypeRuSetup.H => (x : G)) he
  exact heG

private theorem unique_fixed_even_involution : ∀ t : S5,
    t.sign = 1 → t ^ 2 = 1 → t ≠ 1 → ∃! p : Fin 5, t p = p := by
  unfold ExistsUnique
  decide +kernel

private theorem stabilizer_card : ∀ p : Fin 5,
    Fintype.card {g : S5 // g p = p} = 24 := by
  decide +kernel

private theorem centralizer_le_of_normalized_two
    (A P : Subgroup S5) (hA : IsPGroup 2 A)
    (hn : P ≤ normalizer (A : Set S5)) (hP : Nat.card P = 24)
    (t : S5) (htA : t ∈ A) (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (hte : t.sign = 1) :
    centralizer ({t} : Set S5) ≤ P := by
  obtain ⟨p, hp⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by simp)
  have hpt : t p = p := hp ⟨t, htA⟩
  obtain ⟨q, hq, huniq⟩ := unique_fixed_even_involution t hte ht ht1
  have hu : ∀ v, t v = v → v = p := fun v hv => (huniq v hv).trans (huniq p hpt).symm
  let F := MulAction.stabilizer S5 p
  have hPF : P ≤ F := by
    intro g hg
    change g p = p
    apply hu
    have hm : g⁻¹ * t * g ∈ A := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (hn (P.inv_mem hg)) t).mp htA
    have he : (g⁻¹ * t * g) p = p := hp ⟨_, hm⟩
    have he' := congrArg g he
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using he'
  have hPF' : P = F := eq_of_le_of_card_ge hPF (by
    rw [hP]
    change Nat.card {g : S5 // g p = p} ≤ 24
    rw [Nat.card_eq_fintype_card, stabilizer_card])
  rw [hPF']
  intro g hg
  change g p = p
  apply hu
  have he := congrArg (fun a : S5 => a p) (mem_centralizer_singleton_iff.mp hg)
  simpa only [Equiv.Perm.mul_apply, hpt] using he.symm

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

private theorem parabolic_card (d : LocalSetup G) : Nat.card d.parabolic = 49152 := by
  let f := d.parabolicMap
  have he := f.ker.index_mul_card
  rw [index_ker, Nat.card_congr d.parabolicImageEquivS4.toEquiv,
    d.parabolicMap_kernel,
    Nat.card_congr (subgroupOfEquivOfLe (le_inf (pCoreIn_le 2 d.L) d.S_le_H)).toEquiv,
    d.ru1.card_S] at he
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at he
  exact he.symm

/-- The S₅ centralizer lies in the image of the original overlap L ∩ H. -/
theorem s_centralizer_quotient_le_parabolic
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) :
    centralizer ({d.ru2.quotientMap ⟨c.s, d.S_le_H c.s_mem.1⟩} : Set S5) ≤
      (d.L.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap := by
  let f := d.ru2.quotientMap
  let A := (d.toTypeRuSetup.S.subgroupOf d.toTypeRuSetup.H).map f
  let P := (d.L.subgroupOf d.toTypeRuSetup.H).map f
  have hA : IsPGroup 2 A := ((isPGroup_pCoreIn 2 d.L).comap_subtype).map f
  have hnorm : P ≤ normalizer (A : Set S5) := by
    rintro _ ⟨g, hg, rfl⟩
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨g * s * g⁻¹, ?_, by simp⟩
      exact (mem_normalizer_iff.mp (d.ru1.steinberg.normalized hg) s).mp hs
    · intro ha
      have hf : f g * a * (f g)⁻¹ ∈ A := ha
      obtain ⟨s, hs, he⟩ := hf
      refine ⟨g⁻¹ * s * g, ?_, ?_⟩
      · change (g : G)⁻¹ * (s : G) * (g : G) ∈ d.toTypeRuSetup.S
        have hn' := (mem_normalizer_iff.mp
          (d.ru1.steinberg.normalized (d.L.inv_mem hg)) (s : G)).mp hs
        change ((g : G)⁻¹ * (s : G) * ((g : G)⁻¹)⁻¹) ∈ d.toTypeRuSetup.S at hn'
        rw [inv_inv] at hn'
        exact hn'
      · rw [map_mul, map_mul, map_inv, he]
        group
  have hPc : Nat.card P = 24 := by
    have hcard := ConjugateIntersections.card_star_mul_card_inf_Q d d.parabolic inf_le_right
    have hQP : d.toTypeRuSetup.Q ≤ d.parabolic := le_inf d.Q_le_L (pCoreIn_le 2 _)
    rw [inf_eq_right.mpr hQP, d.ru2.card_Q d.card_Z, parabolic_card d] at hcard
    have heq : d.parabolic.subgroupOf d.toTypeRuSetup.H = d.L.subgroupOf d.toTypeRuSetup.H := by
      ext x
      exact ⟨And.left, fun h => ⟨h, x.property⟩⟩
    rw [heq] at hcard
    change Nat.card P * 2048 = 49152 at hcard
    omega
  let sH : d.toTypeRuSetup.H := ⟨c.s, d.S_le_H c.s_mem.1⟩
  have hsKQ := c.s_conjugate_mem_K_sdiff_Q h26 sH.property (IsConj.refl c.s)
  have hs2 : sH ^ 2 = 1 := Subtype.ext (c.s_order_source ▸ pow_orderOf_eq_one c.s)
  apply centralizer_le_of_normalized_two A P hA hnorm hPc (f sH)
    (mem_map_of_mem f c.s_mem.1)
  · rw [← map_pow, hs2, map_one]
  · intro he
    have hm : sH ∈ f.ker := he
    rw [d.ru2.quotient_kernel] at hm
    exact hsKQ.2 hm
  · apply Equiv.Perm.mem_alternatingGroup.mp
    rw [← d.toTypeRuSetup.quotientMap_K]
    exact mem_map_of_mem f hsKQ.1

/-- Pulling the S₅ calculation back through the literal kernel puts C_H(s) in L. -/
theorem H_inf_Gs_le_L (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) :
    d.toTypeRuSetup.H ⊓ c.Gs ≤ d.L := by
  intro x hx
  let xH : d.toTypeRuSetup.H := ⟨x, hx.1⟩
  let sH : d.toTypeRuSetup.H := ⟨c.s, d.S_le_H c.s_mem.1⟩
  have hm : d.ru2.quotientMap xH ∈
      centralizer ({d.ru2.quotientMap sH} : Set S5) := by
    apply mem_centralizer_singleton_iff.mpr
    have he : xH * sH = sH * xH := Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
    simpa only [map_mul] using congrArg d.ru2.quotientMap he
  have hxpre : xH ∈ ((d.L.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap).comap
      d.ru2.quotientMap := c.s_centralizer_quotient_le_parabolic h26 hm
  rw [comap_map_eq, d.ru2.quotient_kernel, sup_of_le_left] at hxpre
  · exact hxpre
  · exact fun q hq => d.Q_le_L hq

/-- The preliminary equality in J.2.7(3), with the original S and s.
The order-seven factor in the J.2.3 centralizer product meets H trivially. -/
theorem H_inf_Gs_eq_Ts_source (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) :
    d.toTypeRuSetup.H ⊓ c.Gs = c.Ts := by
  let singer : SpecialCore.SingerChoice d.toTypeRuSetup c.sylowThree :=
    ⟨c.B7, c.B7_le, c.B7_card, c.B_normalizes⟩
  have h3 := (singer.source_conclusions d c.sylowThree).three c.s c.s_mem c.s_ne_one
  obtain ⟨e, he⟩ := h3.2.1
  have hdis : Disjoint c.B7 d.toTypeRuSetup.H := disjoint_of_coprime_natCard (by
    rw [c.B7_card, d.ru2.card_H d.card_Z]
    decide)
  apply le_antisymm
  · intro x hx
    have hxL : x ∈ d.L ⊓ c.Gs := ⟨c.H_inf_Gs_le_L h26 hx, hx.2⟩
    have hxprod : x ∈ (SpecialCore.fixedCore d.toTypeRuSetup c.B7 : Set G) *
        (SpecialCore.movingCore d.toTypeRuSetup c.B7 c.s : Set G) * (c.B7 : Set G) := by
      rw [← h3.1]
      exact hxL
    obtain ⟨y, hy, b, hb, hxy⟩ := Set.mem_mul.mp hxprod
    obtain ⟨a, ha, m, hm, hay⟩ := Set.mem_mul.mp hy
    have hyTs : y ∈ c.Ts := by
      have hv := (e (⟨a, ha⟩, ⟨m, hm⟩)).property
      rw [he, hay] at hv
      exact hv
    have hbH : b ∈ d.toTypeRuSetup.H := by
      have hv := d.toTypeRuSetup.H.mul_mem (d.toTypeRuSetup.H.inv_mem (d.S_le_H hyTs.1)) hx.1
      rw [← hxy] at hv
      simpa only [inv_mul_cancel_left] using hv
    have hb1 : b = 1 := disjoint_def.mp hdis hb hbH
    rw [hb1, mul_one] at hxy
    exact hxy ▸ hyTs
  · intro x hx
    exact ⟨d.S_le_H hx.1, hx.2⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
