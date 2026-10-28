module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial

/-!
# Finite-model inputs for the cyclic-core reduction

Source: Aschbacher–Smith, printed pp.569–570, after Lemma 2.5.27.
These are identities in the actual automorphism group of A₆. The inner Sylow
subgroup is the intersection with the range of inner automorphisms. The normal
cyclic-four identity and the transposition centralizer are the additional model
calculations; no assertion about the ambient centralizer core is assumed.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction.CoreReduction

open Subgroup

public abbrev A6 := alternatingGroup (Fin 6)
public abbrev AutA6 := MulAut A6

/-- The inner part of an actual Sylow subgroup of `Aut(A₆)`. -/
@[expose] public def innerSylow (P : Sylow 2 AutA6) : Subgroup AutA6 :=
  (P : Subgroup AutA6) ⊓ (MulAut.conj : A6 →* AutA6).range

/-- The concrete finite-model calculations consumed by the reduction.
`transposition` is induced by an actual transposition of the six letters.
Normality of `N` is relative to `P`. The two centralizer identities retain
compatibility with the displayed internal factors. -/
public structure ModelGeometry (P : Sylow 2 AutA6) where
  card : Nat.card (P : Subgroup AutA6) = 32
  dihedral : Nonempty (innerSylow P ≃* DihedralGroup 4)
  rotation : Subgroup AutA6
  rotation_le : rotation ≤ innerSylow P
  transposition : AutA6
  is_transposition : ∃ p : Equiv.Perm (Fin 6), p.IsSwap ∧
    transposition = MulAut.conjNormal p
  transposition_mem : transposition ∈ (P : Subgroup AutA6)
  transposition_square : transposition ^ 2 = 1
  transposition_commutes : transposition ∈ centralizer (innerSylow P : Set AutA6)
  normal_cyclicFour : ∀ N : Subgroup AutA6, N ≤ (P : Subgroup AutA6) →
    (N.subgroupOf (P : Subgroup AutA6)).Normal →
    Nonempty (N ≃* Multiplicative (ZMod 4)) →
    N ⊔ zpowers transposition = rotation ⊔ zpowers transposition
  reflection_rotation : ∀ a ∈ innerSylow P, a ^ 2 = 1 →
    a ∉ (center (innerSylow P)).map (innerSylow P).subtype →
    ∀ y ∈ rotation, a⁻¹ * y * a = y⁻¹
  involution_centralizer : ∀ a ∈ (P : Subgroup AutA6), a ^ 2 = 1 →
    a ∈ centralizer (innerSylow P : Set AutA6) → a ∉ innerSylow P →
    (P : Subgroup AutA6) ⊓ centralizer ({a} : Set AutA6) =
      (P : Subgroup AutA6) ⊓ centralizer ({transposition} : Set AutA6)
  transposition_centralizer :
    (P : Subgroup AutA6) ⊓ centralizer ({transposition} : Set AutA6) =
      zpowers transposition ⊔ innerSylow P
  product : Nonempty ((zpowers transposition ⊔ innerSylow P : Subgroup AutA6) ≃*
    Multiplicative (ZMod 2) × DihedralGroup 4)

private theorem inversion_on_join {Q : Type*} [Group Q]
    (Y R : Subgroup Q) {a : Q}
    (hcomm : Y ≤ centralizer (R : Set Q))
    (hY : ∀ y ∈ Y, a⁻¹ * y * a = y⁻¹)
    (hR : ∀ r ∈ R, a⁻¹ * r * a = r⁻¹) :
    ∀ u ∈ Y ⊔ R, a⁻¹ * u * a = u⁻¹ := by
  have hnormal : (R.subgroupOf (Y ⊔ R)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    exact sup_le (hcomm.trans (centralizer_le_normalizer _)) R.le_normalizer
  let : (R.subgroupOf (Y ⊔ R)).Normal := hnormal
  intro u hu
  have htop : Y.subgroupOf (Y ⊔ R) ⊔ R.subgroupOf (Y ⊔ R) = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have humem : (⟨u, hu⟩ : (Y ⊔ R : Subgroup Q)) ∈ Y.subgroupOf (Y ⊔ R) ⊔ R.subgroupOf (Y ⊔ R) :=
    htop ▸ mem_top _
  obtain ⟨y, hy, r, hr, he⟩ := mem_sup_of_normal_right.mp humem
  have he' : (y : Q) * r = u := congrArg Subtype.val he
  rw [← he']
  calc
    a⁻¹ * ((y : Q) * r) * a = (a⁻¹ * y * a) * (a⁻¹ * r * a) := by group
    _ = (y : Q)⁻¹ * (r : Q)⁻¹ := by rw [hY (y : Q) hy, hR (r : Q) hr]
    _ = ((y : Q) * r)⁻¹ := by
      exact ((show Commute (y : Q) r from (hcomm hy r hr).symm).mul_inv).symm

/-- The normal cyclic-four identity gives inversion in the finite image.
This derives inversion on `N`; it is not a model premise. -/
public theorem ModelGeometry.inverts_normal_cyclicFour {P : Sylow 2 AutA6}
    (m : ModelGeometry P) (N : Subgroup AutA6)
    (hNP : N ≤ (P : Subgroup AutA6))
    (hN : (N.subgroupOf (P : Subgroup AutA6)).Normal)
    (hfour : Nonempty (N ≃* Multiplicative (ZMod 4)))
    {a : AutA6} (ha : a ∈ innerSylow P) (ha2 : a ^ 2 = 1)
    (haZ : a ∉ (center (innerSylow P)).map (innerSylow P).subtype) :
    ∀ n ∈ N, a⁻¹ * n * a = n⁻¹ := by
  have hR : zpowers m.transposition ≤ centralizer (innerSylow P : Set AutA6) :=
    zpowers_le.mpr m.transposition_commutes
  have hcomm : m.rotation ≤ centralizer (zpowers m.transposition : Set AutA6) := by
    intro y hy r hr
    exact (hR hr y (m.rotation_le hy)).symm
  have hRi : ∀ r ∈ zpowers m.transposition, a⁻¹ * r * a = r⁻¹ := by
    intro r hr
    have hr2 : r ^ 2 = 1 := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hr
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        m.transposition_square, one_zpow]
    have har : a * r = r * a := hR hr a ha
    calc
      a⁻¹ * r * a = r := by rw [mul_assoc, ← har, inv_mul_cancel_left]
      _ = r⁻¹ := (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hr2)).symm
  intro n hn
  apply inversion_on_join m.rotation (zpowers m.transposition) hcomm
    (m.reflection_rotation a ha ha2 haZ) hRi
  rw [← m.normal_cyclicFour N hNP hN hfour]
  exact mem_sup_left hn

end CFSG.Quasithin.Chapter2.A6ShadowConstruction.CoreReduction
