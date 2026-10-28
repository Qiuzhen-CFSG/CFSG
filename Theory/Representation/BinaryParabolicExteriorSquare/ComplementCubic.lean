module
public import Theory.Representation.BinaryParabolicExteriorSquare.MarkedCubic
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneRadical
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The cubic fixing the first natural plane

In a basis adapted to the source plane, the common scalar cubic rotates
its complementary plane. It fixes the marked point and preserves the
first exterior three-space. Its fixed indices on the natural, exterior
and dual modules are 4, 16 and 4. On the upper-right radical it acts by
right multiplication by its inverse, with fixed index 16. The coordinate
identity transports this last action to a literal subgroup section.

An order-three lift retains this exact matrix through any two-group
kernel. These results supply the common actor in the 13.8.31 chief count
without changing the natural point or tensor coordinates.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Notation 13.2.1 and 13.8.29–31, printed pp.877 and 964–965. The exterior
model comes from the existing attributed ATLAS bivector implementation.
-/

open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors
public section
namespace Representation.BinaryParabolicExteriorSquare.PlaneSpan
@[expose] def complementCubic : Matrix (Fin 4) (Fin 4) Bit :=
  !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,1]
@[expose] def complementElement : SL(4,Bit) := ⟨complementCubic,by decide⟩
theorem complementElement_order : orderOf complementElement = 3 :=
  orderOf_eq_prime (by decide) (by decide)
theorem exterior_complementCubic (x : Six) :
    exteriorMap complementCubic x = ![x 0,x 2,x 1+x 2,x 4,x 3+x 4,x 5] := by
  ext t
  fin_cases t <;>
    simp [exteriorMap, compound, first, second, complementCubic,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
@[expose] def complementRadicalCubic : Matrix (Fin 4) (Fin 4) Bit :=
  !![1,0,1,0; 0,1,0,1; 1,0,0,0; 0,1,0,0]
theorem complement_radical_matrix (v : PlaneRadical.Four) :
    complementCubic * PlaneRadical.matrix v =
      PlaneRadical.matrix (Matrix.mulVec complementRadicalCubic v) * complementCubic := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complementCubic, complementRadicalCubic, PlaneRadical.matrix,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      add_comm, add_left_comm, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left]

private theorem invariants_card_of_generator {A W : Type*} [Group A] [AddCommGroup W]
    [Module Bit W] (ρ : Representation Bit A W) (a : A)
    (ha : ∀ b, b ∈ Subgroup.zpowers a) :
    Nat.card ρ.invariants = Nat.card {w : W // ρ a w = w} := by
  apply Nat.card_congr
  exact {
    toFun := fun w => ⟨w.val, w.property a⟩
    invFun := fun w => ⟨w.val, (ρ.mem_invariants_iff_of_forall_mem_zpowers a ha w.val).mpr w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem natural_complement_fixedIndex {A : Type*} [Group A]
    (ρ : Representation Bit A (Fin 4 → Bit)) (a : A)
    (ha : ∀ b, b ∈ zpowers a)
    (hact : ∀ v, ρ a v = Matrix.mulVec complementCubic v) :
    BinaryFixedPoints.fixedIndex ρ = 4 := by
  have hc : Nat.card ρ.invariants = 4 := by
    rw [invariants_card_of_generator ρ a ha]
    simp_rw [hact]
    rw [Nat.card_eq_fintype_card]
    decide
  have hm := BinaryFixedPoints.fixedIndex_mul_card ρ
  rw [hc] at hm
  have hv : Nat.card (Fin 4 → Bit) = 16 := by simp [Bit]
  rw [hv] at hm
  omega

theorem exterior_complement_fixedIndex {A : Type*} [Group A]
    (ρ : Representation Bit A Six) (a : A)
    (ha : ∀ b, b ∈ zpowers a)
    (hact : ∀ v, ρ a v = exteriorMap complementCubic v) :
    BinaryFixedPoints.fixedIndex ρ = 16 := by
  have hc : Nat.card ρ.invariants = 4 := by
    rw [invariants_card_of_generator ρ a ha]
    simp_rw [hact, exterior_complementCubic]
    rw [Nat.card_eq_fintype_card]
    decide
  have hm := BinaryFixedPoints.fixedIndex_mul_card ρ
  rw [hc] at hm
  have hv : Nat.card Six = 64 := by simp [Six, Bit]
  rw [hv] at hm
  omega

theorem dual_complement_fixedIndex {A : Type*} [Group A]
    (ρ : Representation Bit A (Fin 4 → Bit)) (a : A)
    (ha : ∀ b, b ∈ zpowers a)
    (hact : ∀ v, ρ a v = Matrix.mulVec complementCubic v) :
    BinaryFixedPoints.fixedIndex ρ.dual = 4 :=
  (BinaryFixedPoints.fixedIndex_dual ρ a ha).trans
    (natural_complement_fixedIndex ρ a ha hact)

theorem radical_complement_fixedIndex {A : Type*} [Group A]
    (ρ : Representation Bit A (Fin 4 → Bit)) (a : A)
    (ha : ∀ b, b ∈ zpowers a)
    (hact : ∀ v, ρ a v = Matrix.mulVec complementRadicalCubic v) :
    BinaryFixedPoints.fixedIndex ρ = 16 := by
  have hc : Nat.card ρ.invariants = 1 := by
    rw [invariants_card_of_generator ρ a ha]
    simp_rw [hact]
    rw [Nat.card_eq_fintype_card]
    decide
  have hm := BinaryFixedPoints.fixedIndex_mul_card ρ
  rw [hc, mul_one] at hm
  exact hm.trans (by simp [Bit])

theorem complementCubic_fixes_plane (v : Fin 4 → Bit) (h2 : v 2 = 0) (h3 : v 3 = 0) :
    Matrix.mulVec complementCubic v = v := by
  ext i
  fin_cases i <;> simp [complementCubic, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h2, h3]

theorem complementCubic_fixes_point :
    Matrix.mulVec complementCubic (Pi.single 0 1) = Pi.single 0 1 := by decide

theorem complementCubic_preserves_first (x : Six) (hx : x ∈ firstSpace) :
    exteriorMap complementCubic x ∈ firstSpace := by
  rw [exterior_complementCubic]
  change _ ∧ _ ∧ _
  simp [hx.1, hx.2.1, hx.2.2]

end Representation.BinaryParabolicExteriorSquare.PlaneSpan


namespace Representation.BinaryParabolicExteriorSquare.PlaneSpan
/-- Retain the exact marked cubic when lifting across a two-group kernel. -/
theorem exists_complement_cubic {G : Type*} [Group G] [Finite G]
    (π : G →* SL(4,Bit)) (hker : IsPGroup 2 π.ker)
    (hcubic : complementElement ∈ π.range) :
    ∃ (A : Subgroup G) (a : A), Nat.card A = 3 ∧
      (∀ b, b ∈ zpowers a) ∧ π a = complementElement := by
  let c : π.range := ⟨complementElement,hcubic⟩
  have hc : orderOf c = 3 := (Subgroup.orderOf_coe c).symm.trans complementElement_order
  have hk : IsPGroup 2 π.rangeRestrict.ker := by
    have he : π.rangeRestrict.ker = π.ker := by ext x; exact Subtype.ext_iff
    rw [he]
    exact hker
  obtain ⟨A,hA,hfi,hcard,_⟩ := π.rangeRestrict.exists_odd_subgroup_lift
    π.rangeRestrict_surjective hk (zpowers c) (by rw [Nat.card_zpowers,hc]; decide)
  have hm : c ∈ A.map π.rangeRestrict := by rw [hA]; exact mem_zpowers c
  obtain ⟨a,ha,he⟩ := hm
  have hac : Nat.card A = 3 := hcard.trans ((Nat.card_zpowers c).trans hc)
  have han : (⟨a,ha⟩ : A) ≠ 1 := by
    intro hh
    have ha1 : a = 1 := congrArg Subtype.val hh
    rw [ha1,map_one] at he
    have hn := congrArg orderOf he
    rw [orderOf_one,hc] at hn
    contradiction
  refine ⟨A,⟨a,ha⟩,hac,?_,congrArg Subtype.val he⟩
  intro b
  rw [zpowers_eq_top_of_prime_card hac han]
  trivial


end Representation.BinaryParabolicExteriorSquare.PlaneSpan

namespace Representation.BinaryParabolicExteriorSquare.PlaneSpan

theorem complement_radical_conjugation (g : PlaneRadical.SL)
    (hg : g.val = complementCubic) (v : PlaneRadical.Four) :
    g * PlaneRadical.element v * g⁻¹ =
      PlaneRadical.element (Matrix.mulVec complementRadicalCubic v) := by
  have he : g * PlaneRadical.element v =
      PlaneRadical.element (Matrix.mulVec complementRadicalCubic v) * g := by
    apply Subtype.ext
    change g.val * PlaneRadical.matrix v =
      PlaneRadical.matrix (Matrix.mulVec complementRadicalCubic v) * g.val
    rw [hg]
    exact complement_radical_matrix v
  rw [he]
  group

theorem section_complement_action
    {G : Type*} [Group G] (H D R Q : Subgroup G) (hDH : D ≤ H) (hRD : R ≤ D)
    (π : H →* PlaneRadical.SL)
    (τ : Representation Bit D PlaneRadical.Four)
    (d : BinaryConjugationSection D R Q τ)
    (hcoordinates : ∀ r : R, PlaneRadical.element (d.coordinates r).toAdd =
      π (inclusion (hRD.trans hDH) r))
    (a : D) (ha : (π (inclusion hDH a)).val = complementCubic)
    (v : PlaneRadical.Four) : τ a v = Matrix.mulVec complementRadicalCubic v := by
  obtain ⟨r,hr⟩ := d.onto (Multiplicative.ofAdd v)
  have hv : (d.coordinates r).toAdd = v := congrArg Multiplicative.toAdd hr
  let rc : R := ⟨(a:G) * r * (a:G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized a.property) r).mp r.property⟩
  have heq : (d.coordinates rc).toAdd = τ a v := by
    exact (d.equivariant a r).trans (congrArg (τ a) hv)
  have he : PlaneRadical.element (τ a v) =
      PlaneRadical.element (Matrix.mulVec complementRadicalCubic v) := by
    rw [←heq,hcoordinates rc]
    have hrc : inclusion (hRD.trans hDH) rc =
        inclusion hDH a * inclusion (hRD.trans hDH) r * (inclusion hDH a)⁻¹ := rfl
    rw [hrc,map_mul,map_mul,map_inv,←hcoordinates r,hv]
    exact complement_radical_conjugation _ ha v
  exact congrArg Multiplicative.toAdd (PlaneRadical.embedding_injective he)

end Representation.BinaryParabolicExteriorSquare.PlaneSpan

