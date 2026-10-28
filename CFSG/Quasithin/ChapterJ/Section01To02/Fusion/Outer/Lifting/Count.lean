module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Count.SectionCounts
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Quotient

/-!
# The 64-element involution fibers and the count 640 in J.2.6

Multiplication by a chosen lift identifies the inverted elements of Q
with the involutions in its literal H/Q fiber. The two free binary
sections give 64 elements in that fiber. A seed and quotient conjugacy
supply every transposition fiber. The actual residual K = O²(H) is the
inverse image of A₅, so these ten fibers partition precisely H − K's
involutions and give the total 640.

The earlier-source containment Q ≤ R₁ and the two freeness calculations
remain the explicit inputs authorized for this count. Its source assembly
belongs to the lifting owner; no fusion of i with iz is used here.

Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem inverting_iff_square (i a : G) (hi : i ^ 2 = 1) :
    i * a * i⁻¹ = a⁻¹ ↔ (a * i) ^ 2 = 1 := by
  constructor
  · intro ha
    calc
      _ = a * (i * a * i⁻¹) * i ^ 2 := by simp only [pow_two]; group
      _ = 1 := by rw [ha, hi, mul_inv_cancel, one_mul]
  · intro ha
    have h : a * (i * a * i⁻¹) = 1 := by
      calc
        _ = (a * i) ^ 2 * (i ^ 2)⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [ha, hi, inv_one, one_mul]
    exact eq_inv_of_mul_eq_one_right h

/-- The cocycles above i are precisely the involutions in the literal H/Q fiber. -/
def involutionFiberEquivInverting (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁)
    (i : d.H) (hiK : (i : G) ∉ d.K) (hi : orderOf (i : G) = 2) :
    involutionFiber d (d.ru2.quotientMap i) ≃ Inverting d.Q (i : G) := by
  have hi2 : (i : G) ^ 2 = 1 := hi ▸ pow_orderOf_eq_one (i : G)
  have hdiff (x : d.H) (hx : d.ru2.quotientMap x = d.ru2.quotientMap i) :
      (x : G) * (i : G)⁻¹ ∈ d.Q := by
    have h : x * i⁻¹ ∈ d.ru2.quotientMap.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
    rw [d.ru2.quotient_kernel] at h
    exact h
  have hne (a : d.Q) : (a : G) * i ≠ 1 := by
    intro h
    apply hiK
    apply Q_le_K_of_le_R₁ d hQR
    rw [eq_inv_of_mul_eq_one_right h]
    exact d.Q.inv_mem a.property
  have hcoord (a : d.Q) :
      d.ru2.quotientMap ⟨(a : G) * i,
        d.H.mul_mem (d.ru2.six.section_le a.property) i.property⟩ =
      d.ru2.quotientMap i := by
    let aH : d.H := ⟨a, d.ru2.six.section_le a.property⟩
    have haH : d.ru2.quotientMap aH = 1 := by
      change aH ∈ d.ru2.quotientMap.ker
      rw [d.ru2.quotient_kernel]
      exact a.property
    change d.ru2.quotientMap (aH * i) = _
    rw [map_mul, haH, one_mul]
  exact {
    toFun := fun x => ⟨⟨(x.val : G) * (i : G)⁻¹, hdiff x.val x.property.2⟩,
      (inverting_iff_square _ _ hi2).mpr (by
        simpa only [inv_mul_cancel_right] using
          (x.property.1 ▸ pow_orderOf_eq_one (x.val : G)))⟩
    invFun := fun a => ⟨⟨(a.val : G) * i,
      d.H.mul_mem (d.ru2.six.section_le a.val.property) i.property⟩,
      orderOf_eq_prime ((inverting_iff_square _ _ hi2).mp a.property) (hne a.val),
      hcoord a.val⟩
    left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; simp
    right_inv := fun a => by apply Subtype.ext; apply Subtype.ext; simp }

/-- A chosen outer involution has exactly 64 involutions in its actual H/Q fiber. -/
theorem card_involutionFiber_of_lift (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁)
    (hZ : Nat.card d.Z = 2) (i : d.H) (hiK : (i : G) ∉ d.K)
    (hi : orderOf (i : G) = 2)
    (hnatural : FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : FreeAt d.ru2.sixAction (d.ru2.quotientMap i)) :
    Nat.card (involutionFiber d (d.ru2.quotientMap i)) = 64 := by
  rw [Nat.card_congr (involutionFiberEquivInverting d hQR i hiK hi)]
  exact card_inverting_Q d hZ i (hi ▸ pow_orderOf_eq_one (i : G)) hnatural hsix

private theorem outside_of_quotient_isSwap (d : TypeRuSetup G) (hQR : d.Q ≤ d.R₁)
    (x : d.H) (hx : (d.ru2.quotientMap x).IsSwap) : (x : G) ∉ d.K := by
  intro h
  have he := (mem_K_iff_quotient_even d hQR x).mp h
  rw [Equiv.Perm.mem_alternatingGroup, hx.sign_eq] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

/-- Every transposition fiber in the actual H/Q map contains exactly 64 involutions.
The only earlier-source premises are Q ≤ R₁, |Z| = 2, a seed, and the two freeness facts. -/
theorem card_involutionFiber (d : LocalSetup G)
    (hQR : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.R₁)
    (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (i₀ : d.toTypeRuSetup.H) (hi₀K : (i₀ : G) ∉ d.toTypeRuSetup.K)
    (hi₀ : orderOf (i₀ : G) = 2)
    (hnatural : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.sixAction (d.ru2.quotientMap i))
    (t : S5) (ht : t.IsSwap) : Nat.card (involutionFiber d.toTypeRuSetup t) = 64 := by
  obtain ⟨i, hi, he⟩ := involutionFiber_nonempty_of_seed d.toTypeRuSetup hQR i₀ hi₀K hi₀ t ht
  have hiK := outside_of_quotient_isSwap d.toTypeRuSetup hQR i (by rw [he]; exact ht)
  rw [← he]
  exact card_involutionFiber_of_lift d.toTypeRuSetup hQR hZ i hiK hi
    (hnatural i hiK hi) (hsix i hiK hi)

/-- Summing the 64-element fibers over the ten actual transpositions gives
exactly 640 involutions outside K = O²(H). -/
theorem card_involutionsOutside (d : LocalSetup G)
    (hQR : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.R₁)
    (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (i₀ : d.toTypeRuSetup.H) (hi₀K : (i₀ : G) ∉ d.toTypeRuSetup.K)
    (hi₀ : orderOf (i₀ : G) = 2)
    (hnatural : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.sixAction (d.ru2.quotientMap i)) :
    Nat.card (involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K) = 640 := by
  classical
  let D := d.toTypeRuSetup
  let F : involutionsOutside D.H D.K → {t : S5 // t.IsSwap} := fun x =>
    ⟨d.ru2.quotientMap ⟨x, x.property.1⟩,
      quotient_isSwap D hQR ⟨x, x.property.1⟩ x.property.2.1 x.property.2.2⟩
  have hc (t : {t : S5 // t.IsSwap}) : Nat.card {x // F x = t} = 64 := by
    let e : {x // F x = t} ≃ involutionFiber D t := {
      toFun := fun x => ⟨⟨x.val.val, x.val.property.1⟩,
        x.val.property.2.2, congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.val.property,
        outside_of_quotient_isSwap D hQR x.val (by rw [x.property.2]; exact t.property),
        x.property.1⟩, Subtype.ext x.property.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
    rw [Nat.card_congr e]
    exact card_involutionFiber d hQR hZ i₀ hi₀K hi₀ hnatural hsix t t.property
  let := Fintype.ofFinite {t : S5 // t.IsSwap}
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Equiv.Perm.card_five_transpositions]

end CFSG.Quasithin.ChapterJ.Fusion.Outer
