module
public import Theory.Representation.ExtraspecialBinarySix.MarkedStabilizer
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer
/-!
# Selecting a cubic fixed plane in an extraspecial binary six-space

A small involution centralizes the normal cubic center: inversion would
have displacement three, exceeding its bound of two. Odd-order
fixed/inverted factorization then supplies a noncentral inverted cubic.
Two conjugate involutions have a common fixed space of dimension at least
two; it fills the cubic's two-dimensional fixed plane. Thus the plane is
fixed pointwise by the original involution.

The source consumer constructs that involution from the original Thompson
image and applies the resulting plane to the extraspecial component marker.
Source: Aschbacher--Smith 15.1.16(c), printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.ExtraspecialBinarySix
variable {D U : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

omit [Finite D] in
/-- Two conjugate involutions saturate the cubic displacement bound. -/
private theorem inverted_cubic_fixed_le (ρ : Representation (ZMod 2) D U)
    (x t : D) (hx : x ^ 3 = 1) (ht : t ^ 2 = 1)
    (hi : t * x * t⁻¹ = x⁻¹)
    (hd : Module.finrank (ZMod 2) U = 6)
    (hc : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) = 2)
    (hr : fixedCodim ρ (zpowers t) ≤ 2) :
    fixedSpace ρ (zpowers x) ≤ fixedSpace ρ (zpowers t) := by
  let b := x * t * x⁻¹
  let A := fixedSpace ρ (zpowers t)
  let B := fixedSpace ρ (zpowers b)
  let C := fixedSpace ρ (zpowers x)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht)
  have he : t * b = x := by
    dsimp only [b]
    calc
      t * (x * t * x⁻¹) = (t * x * t⁻¹) * x⁻¹ := by rw [hti]; group
      _ = x⁻¹ * x⁻¹ := by rw [hi]
      _ = x := by
        apply mul_right_cancel (b := x ^ 2)
        calc
          x⁻¹ * x⁻¹ * x ^ 2 = 1 := by group
          _ = x * x ^ 2 := by rw [←pow_succ']; exact hx.symm
  have hle : A ⊓ B ≤ C := by
    intro v hv
    apply (mem_fixedSpace_zpowers_iff ρ x v).mpr
    rw [←he,map_mul,Module.End.mul_apply,
      (mem_fixedSpace_zpowers_iff ρ b v).mp hv.2,
      (mem_fixedSpace_zpowers_iff ρ t v).mp hv.1]
  have hB := fixedCodim_zpowers_conj ρ t x
  have ha := fixedCodim_add_finrank ρ (zpowers t)
  have hb := fixedCodim_add_finrank ρ (zpowers b)
  have hs := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hu := Submodule.finrank_le (A ⊔ B)
  have hl := Submodule.finrank_mono hle
  have hh : A ⊓ B = C := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    change Module.finrank (ZMod 2) C = 2 at hc
    change fixedCodim ρ (zpowers b) = fixedCodim ρ (zpowers t) at hB
    change fixedCodim ρ (zpowers t) + Module.finrank (ZMod 2) A = _ at ha
    change fixedCodim ρ (zpowers b) + Module.finrank (ZMod 2) B = _ at hb
    omega
  change C ≤ A
  rw [←hh]
  exact inf_le_left


/-- A center-fixing involution supplies an actual noncentral inverted cubic. -/
private theorem exists_inverted_noncentral_cubic
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (t : D) (ht : t ^ 2 = 1)
    (hne : t ∉ centralizer (P : Set D))
    (hZ : t ∈ centralizer ((center P).map P.subtype : Set D)) :
    ∃ x : P, x ∉ center P ∧ x ^ 3 = 1 ∧ t * (x : D) * t⁻¹ = (x : D)⁻¹ := by
  let a : MulAut P := MulAut.conjNormal t
  have ha : Function.Involutive a := by
    intro x
    change ((MulAut.conjNormal t * MulAut.conjNormal t : MulAut P) x) = x
    rw [←map_mul,←pow_two,ht,map_one]
    rfl
  have han : a ≠ 1 := by
    intro he
    apply hne
    intro p hp
    have hh := congrArg Subtype.val (DFunLike.congr_fun he (⟨p,hp⟩ : P))
    change t * p * t⁻¹ = p at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hz : ∀ z ∈ center P, a z = z := by
    intro z hz
    apply Subtype.ext
    change t * (z : D) * t⁻¹ = z
    rw [←hZ z (mem_map_of_mem P.subtype hz),mul_inv_cancel_right]
  have hfixed := MulAut.fixed_eq_center_of_extraspecial27_involution hP a ha han hz
  have hnt : center P ≠ ⊤ := by
    intro he
    have hh := IsExtraspecial.center_order_p 3 P
    rw [he,card_top,hP] at hh
    omega
  obtain ⟨y,hy⟩ := SetLike.exists_not_mem_of_ne_top (center P) hnt
  obtain ⟨⟨c,x⟩,⟨hc,hx,hcx⟩,_⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card
      (show Odd (Nat.card P) by rw [hP]; decide) a ha y
  have hcZ : c ∈ center P := hfixed ▸ ((MulAut.mem_fixedSubgroup a c).mpr hc)
  refine ⟨x,?_,?_,congrArg Subtype.val hx⟩
  · intro hxZ
    exact hy (hcx ▸ (center P).mul_mem hcZ hxZ)
  · simpa only [hexp] using Monoid.pow_exponent_eq_one x

/-- The actual small involution fixes a noncentral cubic's entire fixed plane. -/
private theorem exists_noncentral_cubic_fixed_by_involution
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (hd : Module.finrank (ZMod 2) U = 6)
    (t : D) (ht : orderOf t = 2)
    (hZ : t ∈ centralizer ((center P).map P.subtype : Set D))
    (hr : fixedCodim ρ (zpowers t) ≤ 2) :
    ∃ X : Subgroup P, Nat.card X = 3 ∧ X ≠ center P ∧
      fixedSpace ρ (X.map P.subtype) ≤ fixedSpace ρ (zpowers t) := by
  have hn : t ∉ centralizer (P : Set D) := by
    intro hh
    have hv := P.orderOf_dvd_natCard (centralizer_le ρ P hf hP hd hh)
    rw [ht,hP] at hv
    norm_num at hv
  obtain ⟨x,hx,hx3,hinv⟩ := exists_inverted_noncentral_cubic P hP hexp t
    (ht ▸ pow_orderOf_eq_one t) hn hZ
  have ho : orderOf x = 3 := orderOf_eq_prime hx3 (fun he => hx (he ▸ (center P).one_mem))
  have hc : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers,ho]
  have hXZ : zpowers x ≠ center P := fun he => hx (he ▸ mem_zpowers x)
  refine ⟨zpowers x,hc,hXZ,?_⟩
  have hp := (noncentral_cubic_planes ρ hf P hP hd (zpowers x) hc hXZ).1
  rw [MonoidHom.map_zpowers] at hp ⊢
  exact inverted_cubic_fixed_le ρ x t (congrArg Subtype.val hx3)
    (ht ▸ pow_orderOf_eq_one t) hinv hd hp hr

/-- A small involution fixes the extraspecial center: inversion would move
three dimensions of the faithful six-space. -/
theorem small_involution_centralizes_center
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hd : Module.finrank (ZMod 2) U = 6)
    (t : D) (ht : t ^ 2 = 1) (hr : fixedCodim ρ (zpowers t) ≤ 2) :
    t ∈ centralizer ((center P).map P.subtype : Set D) := by
  let Z := (center P).map P.subtype
  have hZ : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  let σ := ρ.comp P.subtype
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    (hf.comp P.subtype_injective) hP hd
  have hz : fixedSpace ρ Z = ⊥ := by
    rw [←fixedSpace_comp_map]
    change invariants (σ.comp (center P).subtype) = ⊥
    by_contra hh
    have hk := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hh
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff σ).mpr (hf.comp P.subtype_injective)] using hk)
    have hc := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hc
    omega
  obtain ⟨z,hz3⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (by rw [hZ])
  have ho : orderOf (z : D) = 3 := (orderOf_coe z).trans hz3
  have he : zpowers (z : D) = Z := eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    (by rw [Nat.card_zpowers,ho,hZ])
  have hn : (zpowers (z : D)).Normal := by rw [he]; infer_instance
  have hfix : ∀ v, ρ (z : D) v = v → v = 0 := by
    intro v hv
    have hh := (mem_fixedSpace_zpowers_iff ρ z v).mpr hv
    rwa [he,hz,Submodule.mem_bot] at hh
  have hcom : Commute (z : D) t := by
    rcases RankTwo.commute_or_invert_of_normal_three (z : D) t ho hn with hh | hh
    · exact hh
    · have h1 : (ρ (z : D))^3 = 1 := by rw [←map_pow,←ho,pow_orderOf_eq_one,map_one]
      have h2 : ρ t * ρ t = 1 := by rw [←map_mul,←pow_two,ht,map_one]
      have h3 : ρ t * ρ (z : D) = (ρ (z : D))^2 * ρ t := by
        rw [←map_pow,←map_mul,←map_mul,hh]
      have hb := RankTwo.finrank_range_inverting_cubic (ρ (z : D)) (ρ t) h1 hfix h2 h3
      change 2 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = _ at hb
      rw [←fixedCodim_zpowers_eq_displacement_rank] at hb
      omega
  change t ∈ centralizer (Z : Set D)
  rw [←he]
  rintro x ⟨n,rfl⟩
  exact (hcom.zpow_left n).eq

/-- Existence of the compatible cubic requires only the original small
involution and faithful extraspecial six-space, with no fixed-plane premise. -/
theorem exists_noncentral_cubic_fixed_plane
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (hd : Module.finrank (ZMod 2) U = 6)
    (t : D) (ht : orderOf t = 2) (hr : fixedCodim ρ (zpowers t) ≤ 2) :
    ∃ X : Subgroup P, Nat.card X = 3 ∧ X ≠ center P ∧
      fixedSpace ρ (X.map P.subtype) ≤ fixedSpace ρ (zpowers t) :=
  exists_noncentral_cubic_fixed_by_involution ρ hf P hP hexp hd t ht
    (small_involution_centralizes_center ρ hf P hP hd t (ht ▸ pow_orderOf_eq_one t) hr) hr
end Representation.ExtraspecialBinarySix

