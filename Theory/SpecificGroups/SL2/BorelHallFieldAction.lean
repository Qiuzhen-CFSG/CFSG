module
public import Theory.SpecificGroups.SL2.SylowNormalizerTorusAction
public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.Hall.OddKernel
import all Theory.SpecificGroups.SL2.TwoCoreBorel

/-!
# Ordinary field action on a binary Borel Hall subgroup

Preserving an SL₂ Borel preserves its unique unipotent Sylow. Semilinear
coverage then puts the inner factor in the Borel, so the diagonal quotient
sees just the field automorphism. An odd Hall subgroup maps onto the whole
unit quotient; if its order is the unit-group order this character is an
isomorphism. The intertwining identity retains the supplied action on the
original Hall carrier, without selecting or identifying two Cartans.

The original normal-component consumer in Chapter 10 uses this to compare
its Hall action with the tensor exchanger. Source: Aschbacher--Smith 9.2.7,
printed pp.731--732, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
open BenderSuzuki.ZD.Linear
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem borel_preserver_upper (α : MulAut SL(2,F))
    (hB : ∀ x ∈ rankOneBorel F, α x ∈ rankOneBorel F) :
    (upperUnipotent F).map α.toMonoidHom = upperUnipotent F := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have hb := hB x ((upperUnipotent F).le_normalizer hx)
    apply (borelDiagonalProjection_eq_one_iff ⟨α x,hb⟩).mp
    have hx2 : x^2 = 1 := by
      obtain ⟨t,rfl⟩ := (mem_upperUnipotent F _).mp hx
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_two,mul_apply,Fin.sum_univ_two,transvection_coe,CharTwo.add_self_eq_zero]
    have hy2 : (borelDiagonalProjection ⟨α x,hb⟩)^2 = 1 := by
      rw [←map_pow]
      have hh : (⟨α x,hb⟩ : rankOneBorel F)^2 = 1 :=
        Subtype.ext ((map_pow α x 2).symm.trans (congrArg α hx2 |>.trans (map_one α)))
      rw [hh,map_one]
    apply Units.ext
    change (↑(borelDiagonalProjection ⟨α x,hb⟩):F) = 1
    have hh := congrArg Units.val hy2
    change (↑(borelDiagonalProjection ⟨α x,hb⟩):F)^2 = 1 at hh
    rcases sq_eq_one_iff.mp hh with hh|hh
    · exact hh
    · simpa only [CharTwo.neg_eq] using hh
  · rw [card_map_of_injective α.injective]

theorem borel_preserver_field_action (α : MulAut SL(2,F))
    (hB : ∀ x ∈ rankOneBorel F, α x ∈ rankOneBorel F) :
    ∃ σ : F ≃+* F, ∀ x : rankOneBorel F,
      borelDiagonalProjection ⟨α x,hB x x.property⟩ =
        Units.map σ.toMonoidHom (borelDiagonalProjection x) := by
  have hU := borel_preserver_upper α hB
  obtain ⟨g,σ,hα⟩ := sl2_semilinear_coverage α
  have hg : g ∈ rankOneBorel F := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hα] at hU
    change (upperUnipotent F).map
      ((MulAut.conj g).toMonoidHom.comp (sl2FieldAut σ).toMonoidHom) = _ at hU
    rwa [←Subgroup.map_map,sl2FieldAut_map_upper] at hU
  refine ⟨σ,fun x => ?_⟩
  let z : rankOneBorel F := ⟨sl2FieldAut σ x,by
    apply (mem_rankOneBorel_iff _).mpr
    change σ (x.val.val 1 0) = 0
    rw [(mem_rankOneBorel_iff _).mp x.property,map_zero]⟩
  have he : (⟨α x,hB x x.property⟩ : rankOneBorel F) =
      ⟨g,hg⟩ * z * (⟨g,hg⟩ : rankOneBorel F)⁻¹ := by
    apply Subtype.ext
    change α x = g * sl2FieldAut σ x * g⁻¹
    rw [hα]
    rfl
  rw [he,map_mul,map_mul,map_inv,mul_comm (borelDiagonalProjection ⟨g,hg⟩),
    mul_assoc,mul_inv_cancel,mul_one]
  apply Units.ext
  rfl

end Matrix.SpecialLinearGroup

namespace Subgroup.OddHall
variable {A Q : Type*} [Group A] [Group Q]

theorem surjective_restrict_of_odd (B : Subgroup A)
    (hB : IsHallSubgroup oddPrimes B) (f : A →* Q)
    (hf : Function.Surjective f) (hQ : Odd (Nat.card Q)) :
    Function.Surjective (f.comp B.subtype) := by
  have hi : (B.map f).index = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hpi
    have hp2 : p = 2 := by
      by_contra hne
      exact hB.p_in_pi_of_p_dvd_index ⟨p,hp⟩
        (hpi.trans (B.index_map_dvd hf)) hne
    subst p
    exact (Nat.not_even_iff_odd.mpr hQ)
      (even_iff_two_dvd.mpr (hpi.trans (B.map f).index_dvd_card))
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp,range_subtype]
  exact index_eq_one.mp hi

end Subgroup.OddHall

namespace Matrix.SpecialLinearGroup
open BenderSuzuki.ZD.Linear
variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]

theorem hall_borel_field_action (B : Subgroup A)
    (hB : IsHallSubgroup OddHall.oddPrimes B)
    (q : A →* rankOneBorel F) (hq : Function.Surjective q)
    (hcard : Nat.card B = Nat.card F - 1)
    (α : MulAut SL(2,F)) (hα : ∀ x ∈ rankOneBorel F, α x ∈ rankOneBorel F)
    (β : MulAut B) (he : ∀ b : B, (q (β b) : SL(2,F)) = α (q b)) :
    ∃ (χ : B ≃* Fˣ) (σ : F ≃+* F),
      ∀ b : B, χ (β b) = Units.map σ.toMonoidHom (χ b) := by
  let f := borelDiagonalProjection.comp q
  have ho : Odd (Nat.card Fˣ) := by
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨n,_,hn⟩ := FiniteField.card F 2
    rw [Nat.card_units,Nat.card_eq_fintype_card,hn]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow)
      (even_two.pow_of_ne_zero (by exact n.ne_zero)) odd_one
  have hf := OddHall.surjective_restrict_of_odd B hB f
    (borelDiagonalProjection_surjective.comp hq) ho
  let χ := MulEquiv.ofBijective (f.comp B.subtype)
    (hf.bijective_of_nat_card_le (by rw [Nat.card_units,hcard]))
  obtain ⟨σ,hσ⟩ := borel_preserver_field_action α hα
  refine ⟨χ,σ,fun b => ?_⟩
  have hh : q (β b) = ⟨α (q b),hα (q b) (q b).property⟩ := Subtype.ext (he b)
  change borelDiagonalProjection (q (β b)) =
    Units.map σ.toMonoidHom (borelDiagonalProjection (q b))
  rw [hh]
  exact hσ (q b)

end Matrix.SpecialLinearGroup
