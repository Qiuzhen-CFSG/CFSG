module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Fibers
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Quotient
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.CubicFixedPoint
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Count
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CentralProduct

/-!
# The lifting argument before J.2.5

Successive corrections in Q/U and U/Z leave the alternatives i and iz,
with genuine conjugators in H. The quotient calculation uses K = O²(H)
and the preceding Q ≤ R₁ assertion. Cubic fixed-point counting then chooses
the representative inside the literal C_H(B).

The actual ten transposition fibers each have 8 · 4 · 2 = 64 involutions.
The final theorem combines their count with cubic fixed-point counting,
discharging the numerical premise of `centralizing_two_lifts_of_count`.
The freeness premises are produced independently by `qt-j126-module-actions`.
The earlier structural containment is produced by `qt-j12-parabolic-structure`.
The seed is supplied by `exists_outer_seed` after parabolic transport;
the order of Z comes from the preceding J.2.1–3 structure.
The later fusion of i with iz and semidihedral recognition belong to the
J.2.5–6 assembly owner, `qt-j12-fusion-outer`.

Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- The two alternatives before the appeal to J.2.5. The one preceding
structural containment is supplied by R₁ = QS in J.2.2(1). -/
theorem outer_involutions_two_lifts (d : LocalSetup G)
    (hQR : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.R₁)
    (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1)
    (i : d.toTypeRuSetup.H) (hiK : (i : G) ∉ d.toTypeRuSetup.K)
    (hi : orderOf (i : G) = 2)
    (hnatural : FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : FreeAt d.ru2.sixAction (d.ru2.quotientMap i)) :
    ∀ x ∈ involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K,
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = i ∨
        (h : G) * x * (h : G)⁻¹ = (i : G) * z := by
  intro x hx
  let xH : d.toTypeRuSetup.H := ⟨x, hx.1⟩
  obtain ⟨a, ha⟩ := exists_conjugator_quotient d.toTypeRuSetup hQR i xH hiK hi hx.2.1 hx.2.2
  let y := a * xH * a⁻¹
  have hy : (y : G) ^ 2 = 1 := by
    change (MulAut.conj (a : G) x) ^ 2 = 1
    have hx2 : x ^ 2 = 1 := hx.2.2 ▸ pow_orderOf_eq_one x
    rw [← map_pow, hx2, map_one]
  obtain ⟨q, hq⟩ := involution_fiber_two_lifts d.toTypeRuSetup hZ hz hz1 i y
    (hi ▸ pow_orderOf_eq_one (i : G)) hy hnatural hsix ha
  let qH : d.toTypeRuSetup.H := ⟨q, d.ru2.six.section_le q.property⟩
  have he : ((qH * a : d.toTypeRuSetup.H) : G) * x *
      ((qH * a : d.toTypeRuSetup.H) : G)⁻¹ = (q : G) * (y : G) * (q : G)⁻¹ := by
    change ((q : G) * a) * x * ((q : G) * a)⁻¹ =
      (q : G) * ((a : G) * x * (a : G)⁻¹) * (q : G)⁻¹
    group
  exact ⟨qH * a, hq.imp (he.trans ·) (he.trans ·)⟩

/-- The fixed-point and two-lift deductions from the numerical count.
`involution_lifting` below discharges this count from the actual fibers. -/
theorem centralizing_two_lifts_of_count (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQR : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.R₁)
    (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1)
    (hnatural : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.sixAction (d.ru2.quotientMap i))
    (hcard : Nat.card (involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K) = 640) :
    ∃ i : CB d.toTypeRuSetup B,
      (i : G) ∉ d.toTypeRuSetup.K ∧ orderOf (i : G) = 2 ∧
      ∀ x ∈ involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K,
        ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = i ∨
          (h : G) * x * (h : G)⁻¹ = (i : G) * z := by
  obtain ⟨i, hiK, hi⟩ := exists_cubic_centralizing_involution_of_count d.toTypeRuSetup B hcard
  let iH : d.toTypeRuSetup.H := ⟨i, i.property.1⟩
  exact ⟨i, hiK, hi, outer_involutions_two_lifts d hQR hZ hz hz1 iH hiK hi
    (hnatural iH hiK hi) (hsix iH hiK hi)⟩

/-- The involution-lifting portion of J.2.6 before the appeal to J.2.5:
there are exactly 640 outer involutions, and an actual involution in C_H(B)
represents all of them up to H-conjugacy and multiplication by z.

The explicit inputs are the preceding Q ≤ R₁ and |Z| = 2 conclusions,
an outer seed, and freeness on the two literal Ru2 sections. No count,
centralizing witness, semidihedral structure, or fusion of i and iz is assumed. -/
theorem involution_lifting (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQR : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.R₁)
    (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1)
    (i₀ : d.toTypeRuSetup.H) (hi₀K : (i₀ : G) ∉ d.toTypeRuSetup.K)
    (hi₀ : orderOf (i₀ : G) = 2)
    (hnatural : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : ∀ i : d.toTypeRuSetup.H, (i : G) ∉ d.toTypeRuSetup.K →
      orderOf (i : G) = 2 → FreeAt d.ru2.sixAction (d.ru2.quotientMap i)) :
    Nat.card (involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K) = 640 ∧
    ∃ i : CB d.toTypeRuSetup B,
      (i : G) ∉ d.toTypeRuSetup.K ∧ orderOf (i : G) = 2 ∧
      ∀ x ∈ involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K,
        ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = i ∨
          (h : G) * x * (h : G)⁻¹ = (i : G) * z := by
  have hcard := card_involutionsOutside d hQR hZ i₀ hi₀K hi₀ hnatural hsix
  exact ⟨hcard, centralizing_two_lifts_of_count d B hQR hZ hz hz1 hnatural hsix hcard⟩

end CFSG.Quasithin.ChapterJ.Fusion.Outer
