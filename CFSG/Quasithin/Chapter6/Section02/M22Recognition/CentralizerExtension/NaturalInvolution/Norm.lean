module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Mathlib.Tactic.Group

/-!
# The order-three norm in the natural rank-one extension

This supplies the local commutation calculation for the natural `L₂(4)`
extension on printed pp.687–688 (PDF pp.704–705) of Aschbacher–Smith,
`refs/quasithin.pdf`, in Proposition 6.2.13. The quotient and module are
intertwined by `Source.IsNaturalModule`; the kernel is the actual two-core.

Conjugate the image of the Sylow subgroup to the upper root group. A
nonidentity element of order three in its normalizer has nontrivial cubic
diagonal entries. Multiplication by a root element preserves those entries,
so the product has cube one and fixes no nonzero vector. Consequently the
cube of its lift, which lies in the natural module and centralizes the lift,
is trivial. For an involution `x` and the marked element `d`, the relations
`d³ = (xd⁻¹)³ = 1` imply that `x` commutes with `x^d`.

No complement to the two-core is assumed or constructed. The block and
ambient Sylow restrictions are handled by the consuming module.
-/

open Matrix
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension.NaturalInvolution
variable {F : Type*} [Field F]

private theorem triangular_cube_fixed (g : SL(2, F)) (hg : g.val 1 0 = 0)
    (h3 : g.val 0 0 ^ 3 = 1) (hne : g.val 0 0 ≠ 1) :
    g ^ 3 = 1 ∧ ∀ v : Fin 2 → F, g.val *ᵥ v = v → v = 0 := by
  let a := g.val 0 0
  have ha_def : g.val 0 0 = a := rfl
  have hab : a * g.val 1 1 = 1 := by
    simpa only [det_fin_two, hg, mul_zero, sub_zero] using g.property
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have hb : g.val 1 1 = a ^ 2 := by
    apply mul_left_cancel₀ ha
    rw [hab]
    simpa only [pow_succ, mul_comm] using h3.symm
  have hp : a ^ 2 + a + 1 = 0 := by
    have hh : (a - 1) * (a ^ 2 + a + 1) = 0 := by
      calc
        _ = a ^ 3 - 1 := by ring
        _ = 0 := by rw [h3, sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
  have hbne : g.val 1 1 ≠ 1 := by
    intro h
    exact hne (by simpa only [h, mul_one] using hab)
  constructor
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, mul_apply, Fin.sum_univ_two, hg, hb, ha_def]
    · simpa [pow_succ] using h3
    · linear_combination g.val 0 1 * hp + g.val 0 1 * (a + 1) * (h3)
    · calc
        a * a * (a * a) * (a * a) = (a ^ 3) ^ 2 := by ring
        _ = 1 := by rw [h3, one_pow]
  · intro v hv
    have h1 : v 1 = 0 := by
      have he := congrFun hv 1
      have he' : (g.val 1 1 - 1) * v 1 = 0 := by
        have he'' : g.val 1 1 * v 1 = v 1 := by
          simpa [mulVec, dotProduct, Fin.sum_univ_two, hg] using he
        linear_combination he''
      exact (mul_eq_zero.mp he').resolve_left (sub_ne_zero.mpr hbne)
    have h0 : v 0 = 0 := by
      have he := congrFun hv 0
      have he' : (a - 1) * v 0 = 0 := by
        have he'' : a * v 0 = v 0 := by
          simpa [mulVec, dotProduct, Fin.sum_univ_two, h1, a] using he
        linear_combination he''
      exact (mul_eq_zero.mp he').resolve_left (sub_ne_zero.mpr hne)
    ext i
    fin_cases i <;> assumption

private theorem involution_commutes_conjugate {G : Type*} [Group G] (x d : G)
    (hx : x ^ 2 = 1) (hd : d ^ 3 = 1) (hxd : (x * d⁻¹) ^ 3 = 1) :
    Commute x (d⁻¹ * x * d) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)
  have hd2 : d * d = d⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using hd)
  have hnorm : x * (d⁻¹ * x * d) * (d * x * d⁻¹) = 1 := by
    calc
      _ = x * d⁻¹ * x * (d * d) * x * d⁻¹ := by group
      _ = (x * d⁻¹) ^ 3 := by rw [hd2]; simp [pow_succ, mul_assoc]
      _ = 1 := hxd
  have he : x * (d⁻¹ * x * d) = d * x * d⁻¹ := by
    have := eq_inv_of_mul_eq_one_left hnorm
    simpa [hxi, mul_assoc] using this
  have hsq : (x * (d⁻¹ * x * d)) ^ 2 = 1 := by
    rw [he]
    simpa [pow_two, mul_assoc] using congrArg (fun g : G => d * g * d⁻¹) hx
  have hi : (d⁻¹ * x * d)⁻¹ = d⁻¹ * x * d := by simp [hxi, mul_assoc]
  have := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq)
  exact (show (d⁻¹ * x * d) * x = x * (d⁻¹ * x * d) by
    simpa only [_root_.mul_inv_rev, hxi, hi] using this).symm

open SpecialLinearGroup Subgroup

private theorem borel_product [CharP F 2] (x d : SL(2, F))
    (hx : x ∈ upperUnipotent F) (hd : d ∈ rankOneBorel F)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    (x * d) ^ 3 = 1 ∧ ∀ v : Fin 2 → F, (x * d) • v = v → v = 0 := by
  have hd10 := (mem_rankOneBorel_iff d).mp hd
  have hdiag3 : d.val 0 0 ^ 3 = 1 := by
    have h := congrArg (fun g : SL(2, F) => g.val 0 0) hd3
    simpa [pow_succ, mul_apply, Fin.sum_univ_two, hd10, pow_three] using h
  have hd11 : d.val 0 0 * d.val 1 1 = 1 := by
    simpa only [det_fin_two, hd10, mul_zero, sub_zero] using d.property
  have hdiag1 : d.val 0 0 ≠ 1 := by
    intro he
    have he11 : d.val 1 1 = 1 := by simpa [he] using hd11
    have hdu : d = transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (d.val 0 1) := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [transvection_coe, he, he11, hd10]
    have hd2 : d ^ 2 = 1 := by
      rw [hdu, pow_two, ← transvection_add, CharTwo.add_self_eq_zero,
        transvection_coeff_zero]
    apply hd1
    simpa [pow_succ, hd2] using hd3
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F x).mp hx
  have h10 : (transvection zero_ne_one t * d).val 1 0 = 0 := by
    simp [mul_apply, Fin.sum_univ_two, transvection_coe, hd10]
  have h00 : (transvection zero_ne_one t * d).val 0 0 = d.val 0 0 := by
    simp [mul_apply, Fin.sum_univ_two, transvection_coe, hd10]
  obtain ⟨h3, hfix⟩ := triangular_cube_fixed (transvection zero_ne_one t * d) h10
    (h00 ▸ hdiag3) (h00 ▸ hdiag1)
  exact ⟨h3, hfix⟩

private theorem sylow_product [Finite F] [CharP F 2] (S : Sylow 2 (SL(2, F)))
    (x d : SL(2, F)) (hx : x ∈ S) (hd : d ∈ normalizer (S : Set (SL(2, F))))
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    (x * d) ^ 3 = 1 ∧ ∀ v : Fin 2 → F, (x * d) • v = v → v = 0 := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (SL(2, F)) S (upperUnipotentSylow F 2)
  let f := (MulAut.conj a).toMonoidHom
  have hmap : (S : Subgroup (SL(2, F))).map f = upperUnipotent F := by
    exact congrArg Sylow.toSubgroup ha
  have hfx : f x ∈ upperUnipotent F := hmap ▸ mem_map.mpr ⟨x, hx, rfl⟩
  have hfd : f d ∈ rankOneBorel F := by
    change f d ∈ normalizer (upperUnipotent F : Set (SL(2, F)))
    rw [← hmap]
    exact le_normalizer_map f (mem_map.mpr ⟨d, hd, rfl⟩)
  obtain ⟨hc, hf⟩ := borel_product (f x) (f d) hfx hfd
    (by rw [← map_pow, hd3, map_one])
    (fun h => hd1 ((MulAut.conj a).injective (h.trans (map_one f).symm)))
  constructor
  · apply (MulAut.conj a).injective
    change f ((x * d) ^ 3) = f 1
    simpa only [map_pow, map_mul, map_one] using hc
  · intro v hv
    have hh : f (x * d) • (a • v) = a • v := by
      change (a * (x * d) * a⁻¹) • (a • v) = a • v
      simpa only [mul_smul, inv_smul_smul] using congrArg (a • ·) hv
    have hz := hf (a • v) (by simpa only [map_mul] using hh)
    exact (SpecialLinearGroup.toLin' a).injective (hz.trans (map_zero _).symm)

open CFSG.Quasithin.Chapter6.Source

/-- In the actual natural extension, an involution in a Sylow two-subgroup
commutes with its conjugate by an order-three element of its normalizer.
Conjugation follows the source convention `x^d = d⁻¹ * x * d`. -/
public theorem involution_commutes_marked_conjugate {G : Type*} [Group G] [Finite G]
    (L V : Subgroup G) (hV : V = L.pCoreIn 2)
    (hnat : IsNaturalModule L V 2) (S : Sylow 2 L)
    (x d : L) (hx : x ∈ S) (hx2 : x ^ 2 = 1)
    (hd : d ∈ normalizer (S : Set L)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    Commute x (d⁻¹ * x * d) := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnat
  let q : L →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker (g : L) : q g = 1 ↔ g ∈ pCore 2 L := by
    change e (QuotientGroup.mk' (pCore 2 L) g) = 1 ↔ _
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  have hqd : q d ≠ 1 := by
    intro he
    let d₀ : pCore 2 L := ⟨d, (hker d).mp he⟩
    have h3 : d₀ ^ 3 = 1 := Subtype.ext hd3
    have hP : IsPGroup 2 (pCore 2 L) := pCore_isPGroup
    have hc : (orderOf d₀).Coprime 3 := hP.orderOf_coprime (by decide) d₀
    have ho : orderOf d₀ = 1 :=
      hc.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h3)
    exact hd1 (congrArg Subtype.val (orderOf_eq_one_iff.mp ho))
  let S₀ := S.mapSurjective hq
  have hxs : q x ∈ S₀ := mem_map.mpr ⟨x, hx, rfl⟩
  have hds : q d⁻¹ ∈ normalizer (S₀ : Set (SL(2, F))) :=
    le_normalizer_map q (mem_map.mpr ⟨d⁻¹, (normalizer _).inv_mem hd, rfl⟩)
  obtain ⟨h3, hfix⟩ := sylow_product S₀ (q x) (q d⁻¹) hxs hds
    (by rw [← map_pow, inv_pow, hd3, inv_one, map_one])
    (by simpa only [map_inv, inv_ne_one] using hqd)
  let g : L := x * d⁻¹
  have hgker : g ^ 3 ∈ pCore 2 L := (hker _).mp (by
    simpa only [g, map_pow, map_mul] using h3)
  have hgV : ((g ^ 3 : L) : G) ∈ V := by
    rw [hV]
    exact mem_map.mpr ⟨g ^ 3, hgker, rfl⟩
  let v : V := ⟨((g ^ 3 : L) : G), hgV⟩
  have hvfix : (q g) • (Multiplicative.toAdd (f v)) = Multiplicative.toAdd (f v) := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    change ((f.symm (Multiplicative.ofAdd
      (Representation.specialLinearNatural 2 (q g) (Multiplicative.toAdd (f v))))) : G) = _
    calc
      _ = (g : G) * (v : G) * (g : G)⁻¹ := hf g v
      _ = _ := by
        change (g : G) * (v : G) * (g : G)⁻¹ = (f.symm (f v) : G)
        rw [f.symm_apply_apply]
        change (g : G) * ((g ^ 3 : L) : G) * (g : G)⁻¹ = ((g ^ 3 : L) : G)
        simp [pow_succ, mul_assoc]
  have hvzero := hfix (Multiplicative.toAdd (f v))
    (by simpa only [g, map_mul] using hvfix)
  have hvone : v = 1 := f.injective (by
    rw [map_one]
    exact congrArg Multiplicative.ofAdd hvzero)
  have hg3 : g ^ 3 = 1 :=
    Subtype.ext (congrArg (fun v : V => (v : G)) hvone)
  exact involution_commutes_conjugate x d hx2 hd3 hg3

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension.NaturalInvolution
