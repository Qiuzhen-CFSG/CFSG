module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Inner
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Field
public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# Field actors and the endpoint in the natural SU₃ ratio calculation

A genuine coefficient homomorphism has image of order at most two on an
elementary two-group A. Its kernel B lies in L. A moved scalar embeds two
copies of C_V(A) into C_V(B). For B nontrivial the inner calculation therefore
gives codimension at least 4s, whereas rank A ≤ s+1. If B is trivial then
rank A ≤ 1, while semilinear descent gives codimension at least 3s.
Both inequalities exclude ratio at most two for every s ≥ 2, including s=2.

The coefficient action and the assertion that linear involutions lie in L
are explicit normalizer inputs. Their construction from the actual marked
natural module is a separate prerequisite; this module does not assert K.3.3
without that construction. Source: Aschbacher–Smith, K.3.3, printed p.456.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki.MatrixGroups Subgroup Representation Representation.BinaryOffender
open scoped ENNReal
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Actual coefficient action of the original group on its natural SU₃ coordinates.
The final clause concerns only linear involutions, and contains no ratio conclusion. -/
structure UnitarySemilinearControl (M : UnitaryModel J ρ L) where
  coefficient : G →* (F ≃+* F)
  semilinear : ∀ (g : G) (c : F) (v : Fin 3 → F),
    M.coordinateAction g (c • v) = coefficient g c • M.coordinateAction g v
  linear_involution : ∀ g : G, g ^ 2 = 1 → coefficient g = 1 → g ∈ L

namespace UnitarySemilinearControl
variable {M : UnitaryModel J ρ L} (C : UnitarySemilinearControl M)

/-- An involution outside the actual layer has nontrivial coefficient action. -/
theorem outer_coefficient_ne_one {t : G} (ht : t ^ 2 = 1) (hL : t ∉ L) :
    C.coefficient t ≠ 1 := fun he => hL (C.linear_involution t ht he)

/-- The coefficient of an outer involution has exact order two. -/
theorem outer_coefficient_order {t : G} (ht : t ^ 2 = 1) (hL : t ∉ L) :
    orderOf (C.coefficient t) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ht, map_one]
  · exact C.outer_coefficient_ne_one ht hL

variable [Finite F]

/-- The nontrivial coefficient involution is exactly the stored Hermitian conjugation. -/
theorem outer_coefficient_eq_conj {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s))
    {t : G} (ht : t ^ 2 = 1) (hL : t ∉ L) : C.coefficient t = J.conj := by
  apply J.field_involution_eq_conj s hs hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj)
  · rw [← map_pow, ht, map_one]
  · exact C.outer_coefficient_ne_one ht hL

include C in
/-- The explicit field part of an outer involution on the marked column module. -/
theorem outer_semilinear {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s))
    {t : G} (ht : t ^ 2 = 1) (hL : t ∉ L) (c : F) (v : Fin 3 → F) :
    M.coordinateAction t (c • v) = c ^ (2 ^ s) • M.coordinateAction t v := by
  rw [C.semilinear, C.outer_coefficient_eq_conj hs hcard hconj ht hL, hconj]

include C in
/-- An outer involution moves exactly half of the binary natural module. -/
theorem outer_fixedCodim {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2)
    {t : G} (ht : t ^ 2 = 1) (hL : t ∉ L) :
    fixedCodim ρ (zpowers t) = 3 * s := by
  have htorder : orderOf t = 2 := orderOf_eq_prime ht (fun he => hL (he ▸ L.one_mem))
  have hd := FiniteFieldSemilinearDisplacement.fixedCodim_formula
    M.coordinateAction (by decide : 0 < 2) t htorder
    (C.coefficient t) (C.outer_coefficient_order ht hL) (C.semilinear t)
  rw [UnitaryModel.field_finrank hcard] at hd
  simp at hd
  rw [M.fixedCodim_eq]
  omega

/-- Two copies of the common fixed space fit into the fixed space of the
coefficient kernel. This retains the extra fixed-space loss at s=2. -/
theorem fixedSpace_card_square_le {A B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≤ C.coefficient.ker) {t : G} (htA : t ∈ A)
    (hne : C.coefficient t ≠ 1) :
    Nat.card (fixedSpace M.coordinateAction A) ^ 2 ≤
      Nat.card (fixedSpace M.coordinateAction B) := by
  obtain ⟨c, hc⟩ : ∃ c, C.coefficient t c ≠ c := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  have hfixed (v : fixedSpace M.coordinateAction A) :
      M.coordinateAction t v.val = v.val := v.property ⟨t, htA⟩
  let f : fixedSpace M.coordinateAction A × fixedSpace M.coordinateAction A →
      fixedSpace M.coordinateAction B := fun x => ⟨x.1.val + c • x.2.val, by
    intro b
    change M.coordinateAction b.val (x.1.val + c • x.2.val) = _
    rw [map_add, C.semilinear, show C.coefficient b.val = 1 from hB b.property,
      RingAut.one_apply, show M.coordinateAction b.val x.1.val = x.1.val from
        x.1.property ⟨b.val, hBA b.property⟩,
      show M.coordinateAction b.val x.2.val = x.2.val from x.2.property ⟨b.val, hBA b.property⟩]⟩
  have hf : Function.Injective f := by
    intro x y he
    have he := congrArg Subtype.val he
    change x.1.val + c • x.2.val = y.1.val + c • y.2.val at he
    have he' := congrArg (M.coordinateAction t) he
    simp only [map_add, C.semilinear, hfixed] at he'
    have hz : (C.coefficient t c - c) • (x.2.val - y.2.val) = 0 := by
      calc
        _ = ((x.1.val + C.coefficient t c • x.2.val) - (y.1.val + C.coefficient t c • y.2.val)) -
            ((x.1.val + c • x.2.val) - (y.1.val + c • y.2.val)) := by
          simp only [sub_smul, smul_sub]
          abel
        _ = 0 := by rw [he, he']; simp
    have h2 : x.2.val = y.2.val :=
      sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc))
    have h1 : x.1.val = y.1.val := by rw [h2] at he; exact add_right_cancel he
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective f hf

/-- The same comparison as a binary dimension inequality. -/
theorem twice_fixed_finrank_le {A B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≤ C.coefficient.ker) {t : G} (htA : t ∈ A)
    (hne : C.coefficient t ≠ 1) :
    2 * Module.finrank (ZMod 2) (fixedSpace M.coordinateAction A) ≤
      Module.finrank (ZMod 2) (fixedSpace M.coordinateAction B) := by
  have hd := C.fixedSpace_card_square_le hBA hB htA hne
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace M.coordinateAction A),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace M.coordinateAction B),
    Nat.card_zmod, ← pow_mul] at hd
  exact (Nat.mul_comm _ _).trans_le ((Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hd)

variable [Finite G] [L.Normal] [FiniteDimensional (ZMod 2) V]
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2)
  (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s))
include C hJ hs hcard hconj

/-- All outer elementary actors have ratio strictly greater than two, including s=2. -/
theorem elementary_le_layer {A : Subgroup G} (hA : IsElementaryTwo A)
    (hratio : actionRatio ρ A ≤ 2) : A ≤ L := by
  let : IsElementaryAbelian 2 A := hA.2
  by_contra hn
  obtain ⟨t, htA, htL⟩ := Set.not_subset.mp hn
  have ht : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  have htcoeff := C.outer_coefficient_ne_one ht htL
  let B := A ⊓ C.coefficient.ker
  have hBA : B ≤ A := inf_le_left
  have hBL : B ≤ L := by
    intro b hb
    exact C.linear_involution b (elemPow_eq_one_of_isElementaryAbelian b hb.1) hb.2
  have hindex : B.relIndex A ≤ 2 := by
    let : IsCyclic (F ≃+* F) := SL2NaturalOffenders.binaryFieldAut_isCyclic
    let : IsElementaryAbelian 2 (A.map C.coefficient) := IsElementaryAbelian.map _
    change (A ⊓ C.coefficient.ker).relIndex A ≤ 2
    rw [inf_relIndex_left, relIndex_ker]
    have hd := IsElementaryAbelian.exponent_dvd_p 2 (A.map C.coefficient)
    rw [IsCyclic.exponent_eq_card] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hcount : Nat.card B * B.relIndex A = Nat.card A := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) B A bot_le hBA
  have hcardA : Nat.card A ≤ Nat.card B * 2 := by
    rw [← hcount]
    exact Nat.mul_le_mul_left _ hindex
  have hr := (actionRatio_le_nat_iff ρ hA 2).mp hratio
  by_cases hB : B = ⊥
  · have ha : rank A ≤ 1 := by
      rw [hB, card_bot, one_mul, hA.card_eq_two_pow_rank] at hcardA
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
        (by simpa only [pow_one] using hcardA)
    have htbound : fixedCodim ρ (zpowers t) ≤ fixedCodim ρ A :=
      NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr htA)
    rw [C.outer_fixedCodim hcard ht htL] at htbound
    omega
  · have hBe : IsElementaryTwo B := hA.of_le hBA hB
    have hrB := M.elementary_rank_le hJ hs hcard hconj hBe hBL
    have hrA : rank A ≤ s + 1 := by
      rw [hA.card_eq_two_pow_rank, hBe.card_eq_two_pow_rank] at hcardA
      have hp : 2 ^ rank A ≤ 2 ^ (s + 1) := by
        calc
          _ ≤ 2 ^ rank B * 2 := hcardA
          _ ≤ 2 ^ s * 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hrB)
          _ = _ := (pow_succ _ _).symm
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hp
    have hdimB := fixedCodim_add_finrank M.coordinateAction B
    have hdimA := fixedCodim_add_finrank M.coordinateAction A
    have hcodB : fixedCodim M.coordinateAction B = 2 * s :=
      (M.fixedCodim_eq B).symm.trans (M.elementary_fixedCodim hJ hs hcard hconj hBe hBL)
    have hdim : Module.finrank (ZMod 2) (Fin 3 → F) = 6 * s := by
      rw [Module.finrank_pi_fintype, UnitaryModel.field_finrank hcard]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    have htwice := C.twice_fixed_finrank_le hBA (show B ≤ C.coefficient.ker from inf_le_right) htA htcoeff
    rw [hcodB, hdim] at hdimB
    rw [hdim] at hdimA
    rw [M.fixedCodim_eq] at hr
    omega

end UnitarySemilinearControl
end CFSG.Quasithin.ChapterK.RankOne
