module

public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModelFixed
public import Theory.GroupAction.ElementaryTwoTernaryLine
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PGroup.ExtraspecialThreeNormalizerGeneration
public import Theory.SpecificGroups.HeisenbergPrime.Recognition
public import Theory.SpecificGroups.HeisenbergPrime.SquareRootCenter

/-!
# A Sylow square root of the original extraspecial involution

An elementary two-group preserves a line on the ternary Frattini plane,
so the irreducible Sylow actor contains an element of order four. Its
automorphism of the extraspecial group fixes the center. The square and
the given center-fixing involution differ by an element of the odd normal
extraspecial group, so they agree inside the Sylow two-subgroup.

The residual specialization obtains self-centralization from the trivial
two-core of the actual whole action. No square-root witness, center
movement, or global Thompson residual conclusion is assumed.

Source application: Aschbacher--Smith 15.1.2 and 15.1.13--14,
printed pp.1086 and 1090--1091.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
variable {D : Type*} [Group D] [Finite D]

/-- Irreducibility on the ternary Frattini plane forces an actual element
of order four in the original Sylow actor. -/
theorem sylow_exists_order_four_of_frattini_irreducible
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (S : Sylow 2 D)
    (hI : ChapterD.Section03.FrattiniIrreducible (S : Subgroup D)
      P le_normalizer_of_normal) :
    ∃ x ∈ (S : Subgroup D), orderOf x = 4 := by
  have hQ : Nat.card (P ⧸ frattini P) = 9 := by
    have hc := (frattini P).card_eq_card_quotient_mul_card_subgroup
    have hphi : Nat.card (frattini P) = 3 := by
      rw [IsExtraspecial.frattini_eq_center_three, IsExtraspecial.center_order_p 3 P]
    rw [hphi, hP] at hc
    omega
  have hnot : ¬ IsElementaryAbelian 2 S := by
    intro hS
    let := hS
    obtain ⟨A, hA, hstable⟩ := MulAut.exists_stable_three_of_elementary_two
      (ChapterD.Section03.frattiniAction (S : Subgroup D) P le_normalizer_of_normal) hQ
    rcases hI A hstable with hb | ht
    · rw [hb, card_bot] at hA
      omega
    · rw [ht, card_top, hQ] at hA
      omega
  have hsquare : ∃ a : S, a ^ 2 ≠ 1 := by
    by_contra! hs
    apply hnot
    exact {
      toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
        (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  obtain ⟨a, ha⟩ := hsquare
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_orderOf_eq_pow a
  have hn2 : 2 ≤ n := by
    by_contra hh
    have hh' : n = 0 ∨ n = 1 := by omega
    rcases hh' with rfl | rfl
    · have he : a = 1 := orderOf_eq_one_iff.mp hn
      exact ha (by rw [he, one_pow])
    · exact ha (by simpa only [pow_one, hn] using pow_orderOf_eq_one a)
  let x : S := a ^ (orderOf a / 4)
  have hx : orderOf x = 4 := orderOf_pow_orderOf_div
    (by rw [hn]; positivity) (by rw [hn]; exact pow_dvd_pow 2 hn2)
  exact ⟨x, x.property, (Subgroup.orderOf_coe x).trans hx⟩

/-- A center-fixing involution of the self-centralizing extraspecial group
is the square of an actual center-fixing element in the same Sylow actor. -/
theorem sylow_square_root_of_center_fixing_involution
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (hC : centralizer (P : Set D) ≤ P) (S : Sylow 2 D)
    (hI : ChapterD.Section03.FrattiniIrreducible (S : Subgroup D)
      P le_normalizer_of_normal)
    (t : D) (htS : t ∈ (S : Subgroup D)) (ht : orderOf t = 2)
    (htC : t ∈ centralizer ((center P).map P.subtype : Set D)) :
    ∃ x ∈ (S : Subgroup D), orderOf x = 4 ∧ x ^ 2 = t ∧
      x ∈ centralizer ((center P).map P.subtype : Set D) := by
  have hdis : Disjoint P (S : Subgroup D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hP, hn]
    exact (by decide : Nat.Coprime 27 2).pow_right n
  have hodd (a : D) (haP : a ∈ P) (haS : a ∈ (S : Subgroup D)) : a = 1 :=
    mem_bot.mp (hdis.eq_bot ▸ (show a ∈ P ⊓ (S : Subgroup D) from ⟨haP, haS⟩))
  obtain ⟨e⟩ := HeisenbergPrime.nonempty_mulEquiv_of_card_prime_cube
    (show Nat.card P = 3 ^ 3 by simpa using hP)
    (fun a : P => hexp ▸ Monoid.pow_exponent_eq_one a)
    (IsExtraspecial.commutator_eq_center (p := 3) (P := P)).le (by
      intro hcomm
      let := hcomm
      have hh := IsExtraspecial.center_order_p 3 P
      rw [center_eq_top, card_top, hP] at hh
      omega)
  obtain ⟨x, hxS, hx⟩ := sylow_exists_order_four_of_frattini_irreducible P hP S hI
  have hx4 : x ^ 4 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx2 : x ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hx] at hd
    norm_num at hd
  have hα4 : (MulAut.conjNormal x : MulAut P) ^ 4 = 1 := by
    rw [← map_pow, hx4, map_one]
  have hα2 : (MulAut.conjNormal x : MulAut P) ^ 2 ≠ 1 := by
    intro he
    have hc : x ^ 2 ∈ centralizer (P : Set D) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer P]
      change (MulAut.conjNormal (x ^ 2) : MulAut P) = 1
      rwa [map_pow]
    exact hx2 (hodd (x ^ 2) (hC hc) ((S : Subgroup D).pow_mem hxS 2))
  have hfix := IsExtraspecial.order_four_aut_fixes_center e
    (MulAut.conjNormal x) hα4 hα2
  have hxC : x ∈ centralizer ((center P).map P.subtype : Set D) := by
    rintro z ⟨w, hw, rfl⟩
    have he := congrArg P.subtype (hfix w hw)
    change x * (w : D) * x⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htne : t ≠ 1 := by intro he; simp [he] at ht
  have hx2C : ∀ z ∈ center P, (MulAut.conjNormal (x ^ 2) : MulAut P) z = z := by
    intro z hz
    rw [map_pow]
    change MulAut.conjNormal x (MulAut.conjNormal x z) = z
    rw [hfix z hz, hfix z hz]
  have htfix : ∀ z ∈ center P, (MulAut.conjNormal t : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    change t * (z : D) * t⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr
      (htC z (mem_map_of_mem P.subtype hz)).symm
  have hproduct : x ^ 2 * t ∈ P := IsExtraspecial.involution_mul_mem_of_card27
    P hP hC (x ^ 2) t ⟨hx2, by rw [← pow_mul]; exact hx4⟩ ⟨htne, ht2⟩ hx2C htfix
  have hprod : x ^ 2 * t = 1 := hodd _ hproduct
    ((S : Subgroup D).mul_mem ((S : Subgroup D).pow_mem hxS 2) htS)
  have hsquare : x ^ 2 = t := by
    calc
      x ^ 2 = t⁻¹ := eq_inv_of_mul_eq_one_left hprod
      _ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht2)
  exact ⟨x, hxS, hx, hsquare, hxC⟩

/-- For the actual extraspecial two-residual, trivial two-core discharges
the self-centralization needed by the Sylow square-root construction. -/
theorem residual_sylow_square_root_of_center_fixing_involution
    (hcore : pCore 2 D = ⊥) [IsExtraspecial 3 (pResidual 2 D)]
    (hP : Nat.card (pResidual 2 D) = 27)
    (hexp : Monoid.exponent (pResidual 2 D) = 3) (S : Sylow 2 D)
    (hI : ChapterD.Section03.FrattiniIrreducible (S : Subgroup D)
      (pResidual 2 D) le_normalizer_of_normal)
    (t : D) (htS : t ∈ (S : Subgroup D)) (ht : orderOf t = 2)
    (htC : t ∈ centralizer ((center (pResidual 2 D)).map
      (pResidual 2 D).subtype : Set D)) :
    ∃ x ∈ (S : Subgroup D), orderOf x = 4 ∧ x ^ 2 = t ∧
      x ∈ centralizer ((center (pResidual 2 D)).map (pResidual 2 D).subtype : Set D) :=
  sylow_square_root_of_center_fixing_involution (pResidual 2 D) hP hexp
    (centralizer_pResidual_le_of_pCore_eq_bot hcore) S hI t htS ht htC

open Representation Representation.BinaryOffender
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The original extraspecial action has at most one Sylow-fixed dimension
when its Sylow actor moves the center. The actual square root is constructed
from irreducibility, rather than supplied as a premise. -/
theorem residual_sylow_fixed_dimension_le_one
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) [IsExtraspecial 3 (pResidual 2 D)]
    (hP : Nat.card (pResidual 2 D) = 27)
    (hexp : Monoid.exponent (pResidual 2 D) = 3)
    (h6 : Module.finrank (ZMod 2) W = 6) (S : Sylow 2 D)
    (hI : ChapterD.Section03.FrattiniIrreducible (S : Subgroup D)
      (pResidual 2 D) le_normalizer_of_normal)
    (t : D) (htS : t ∈ (S : Subgroup D)) (ht : orderOf t = 2)
    (hr : fixedCodim ρ (zpowers t) = 2)
    (hm : ¬ (S : Subgroup D) ≤ centralizer
      ((center (pResidual 2 D)).map (pResidual 2 D).subtype : Set D)) :
    Module.finrank (ZMod 2) (fixedSpace ρ (S : Subgroup D)) ≤ 1 := by
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htC := ExtraspecialBinarySix.small_involution_centralizes_center ρ hf
    (pResidual 2 D) hP h6 t ht2 hr.le
  obtain ⟨x, hxS, _, hxt, hxc⟩ :=
    residual_sylow_square_root_of_center_fixing_involution hcore hP hexp S hI t htS ht htC
  exact extraspecial_sylow_fixed_dimension_le_one_of_square_root ρ hf
    (pResidual 2 D) hP h6 (S : Subgroup D) x t hxS ht2 hxt hxc hr hm

end CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
