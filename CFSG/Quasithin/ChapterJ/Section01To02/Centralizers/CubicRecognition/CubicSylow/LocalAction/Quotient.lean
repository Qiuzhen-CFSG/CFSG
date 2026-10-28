module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Actions
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The faithful transitive action on the literal R/B

The involution z centralizes B. A coset fixed by z has displacement in B;
applying z twice shows that this displacement has both square and cube one.
It is therefore trivial, and C_R(z) = B shows that only the identity coset
is fixed. This argument uses the original quotient map and action.

If a rotation has eighth power one and fourth power z, every nonidentity
coset has period eight. The quotient has nine elements, so those powers
are transitive on its eight nonidentity elements. A two-group with center
<z> consequently acts faithfully on this quotient as well.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

public section


noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Conjugation by the original z fixes the kernel B pointwise. -/
theorem action_z_fixed_of_mem_B
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (hzT : c.z ∈ TR c R Tplus)
    (x : ambient c R) (hx : (x : G) ∈ c.B) : action c R Tplus ⟨c.z, hzT⟩ x = x := by
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mpr (c.z_mem_GB (x : G) hx).symm

/-- The only z-fixed coset of the literal R/B is its identity. -/
theorem quotientAction_z_fixed_iff (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (hzT : c.z ∈ TR c R Tplus)
    (u : Quotient c R) : quotientAction c R Tplus ⟨c.z, hzT⟩ u = u ↔ u = 1 := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (c.B.subgroupOf (ambient c R)) u
    let a := action c R Tplus ⟨c.z, hzT⟩
    have hd : (a x / x : ambient c R) ∈ c.B.subgroupOf (ambient c R) :=
      QuotientGroup.eq_iff_div_mem.mp h
    have ha2 : a ^ 2 = 1 := by
      change action c R Tplus ⟨c.z, hzT⟩ ^ 2 = 1
      rw [← map_pow, show (⟨c.z, hzT⟩ : TR c R Tplus) ^ 2 = 1 from
        Subtype.ext (hz ▸ pow_orderOf_eq_one c.z), map_one]
    have haa : a (a x) = x := congrArg (fun t : MulAut (ambient c R) => t x) ha2
    have hfixed : a (a x / x) = a x / x := action_z_fixed_of_mem_B c R Tplus hzT _ hd
    have hi : a x / x = (a x / x)⁻¹ := by
      calc
        a x / x = a (a x / x) := hfixed.symm
        _ = x / a x := by rw [map_div, haa]
        _ = (a x / x)⁻¹ := (inv_div _ _).symm
    have hd2 : (a x / x) ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun y => y * (a x / x)) hi).trans (inv_mul_cancel _)
    have hd3 : (a x / x) ^ 3 = 1 := by
      apply Subtype.ext
      exact orderOf_dvd_iff_pow_eq_one.mp (hB ▸ c.B.orderOf_dvd_natCard hd)
    have hdone : a x / x = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
        (orderOf_dvd_of_pow_eq_one hd2) (orderOf_dvd_of_pow_eq_one hd3))
    have hax : a x = x := div_eq_one.mp hdone
    apply (QuotientGroup.eq_one_iff _).mpr
    change (x : G) ∈ c.B
    rw [← centralizer_z_eq c hB P hP R]
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hax)).symm
  · rintro rfl
    exact map_one _
/-- The original quotient has exactly nine elements. -/
theorem quotient_card
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) : Nat.card (Quotient c R) = 9 := by
  rw [Nat.card_congr (ambientQuotientEquiv c e R).toEquiv]
  simp [AlternatingSix.M10.LocalGeometry.NineCoordinates]


/-- There are eight nonidentity cosets, independently of the exponent of R. -/
theorem quotient_nonidentity_card
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) : Nat.card {u : Quotient c R // u ≠ 1} = 8 := by
  classical
  let : Fintype (Quotient c R) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun u : Quotient c R => u = 1),
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, quotient_card c e R]

/-- Powers of the marked rotation give the required transitivity on (R/B)#. -/
theorem quotient_transitive_of_rotation (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (r : TR c R Tplus)
    (hr8 : (r : G) ^ 8 = 1) (hr4 : (r : G) ^ 4 = c.z)
    (u v : Quotient c R) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ t : TR c R Tplus, quotientAction c R Tplus t u = v := by
  let a := quotientAction c R Tplus r
  have hit (n : ℕ) (x : Quotient c R) : (fun y => a y)^[n] x = (a ^ n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      exact congrArg a ih
  have ha8 : a ^ 8 = 1 := by
    change quotientAction c R Tplus r ^ 8 = 1
    rw [← map_pow, show r ^ 8 = 1 from Subtype.ext hr8, map_one]
  have hzT : c.z ∈ TR c R Tplus := hr4 ▸ (TR c R Tplus).pow_mem r.property 4
  have hr4' : r ^ 4 = ⟨c.z, hzT⟩ := Subtype.ext hr4
  have hperiod : Function.minimalPeriod (fun x => a x) u = 8 := by
    apply Function.minimalPeriod_eq_prime_pow (p := 2) (k := 2)
    · intro h
      apply hu
      apply (quotientAction_z_fixed_iff c hB P hP hz R Tplus hzT u).mp
      change (fun x => a x)^[4] u = u at h
      rw [hit] at h
      change (quotientAction c R Tplus r ^ 4) u = u at h
      simpa only [← map_pow, hr4'] using h
    · change (fun x => a x)^[8] u = u
      rw [hit, ha8]
      rfl
  let f : Fin 8 → {x : Quotient c R // x ≠ 1} := fun i =>
    ⟨(a ^ i.val) u, fun h => hu ((a ^ i.val).injective (h.trans (map_one (a ^ i.val)).symm))⟩
  have hinj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := fun x => a x) (x := u)
      (by simpa only [hperiod] using i.isLt) (by simpa only [hperiod] using j.isLt)).mp
    rw [hit, hit]
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by rw [Nat.card_fin, quotient_nonidentity_card c e R]⟩ |>.surjective
  obtain ⟨i, hi⟩ := hsurj ⟨v, hv⟩
  refine ⟨r ^ i.val, ?_⟩
  rw [map_pow]
  exact congrArg Subtype.val hi

/-- The marked involution has nontrivial action on the quotient. -/
theorem quotientAction_z_ne_one (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (hzT : c.z ∈ TR c R Tplus) :
    quotientAction c R Tplus ⟨c.z, hzT⟩ ≠ 1 := by
  let : Nontrivial (Quotient c R) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [quotient_card c e R]
    decide)
  obtain ⟨u, hu⟩ := exists_ne (1 : Quotient c R)
  intro he
  apply hu
  apply (quotientAction_z_fixed_iff c hB P hP hz R Tplus hzT u).mp
  rw [he]
  rfl

/-- A marked center makes the original T_R-action on R/B faithful. -/
theorem quotientAction_injective_of_center (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (hcenter : (center (TR c R Tplus)).map (TR c R Tplus).subtype = zpowers c.z) :
    Function.Injective (quotientAction c R Tplus) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hker
  let : Nontrivial (quotientAction c R Tplus).ker := (nontrivial_iff_ne_bot _).mpr hker
  let : Fact (IsPGroup 2 (TR c R Tplus)) := ⟨TR_isPGroup c R Tplus⟩
  obtain ⟨x, hx, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) (quotientAction c R Tplus).ker
  have hmem : ((x : TR c R Tplus) : G) ∈ zpowers c.z :=
    hcenter ▸ mem_map_of_mem (TR c R Tplus).subtype hc
  rw [mem_zpowers_iff_mem_range_orderOf, hz, Finset.mem_image] at hmem
  obtain ⟨n, hn, he⟩ := hmem
  have hn' : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · apply hx
    apply Subtype.ext
    apply Subtype.ext
    change ((x : TR c R Tplus) : G) = 1
    simpa only [pow_zero] using he.symm
  · have hez : ((x : TR c R Tplus) : G) = c.z := by
      simpa only [pow_one] using he.symm
    have hzT : c.z ∈ TR c R Tplus := hez ▸ (x : TR c R Tplus).property
    have hxz : (x : TR c R Tplus) = ⟨c.z, hzT⟩ := Subtype.ext hez
    apply quotientAction_z_ne_one c hB P hP hz e R Tplus hzT
    rw [← hxz]
    exact x.property

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction
