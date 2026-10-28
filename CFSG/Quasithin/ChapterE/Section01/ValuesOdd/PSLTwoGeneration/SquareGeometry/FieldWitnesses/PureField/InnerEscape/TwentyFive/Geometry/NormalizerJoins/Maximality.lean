module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair.SubfieldMaximality

/-!
# Maximal centralizers in characteristic five

Projective descent conjugates each of the two actual field-involution
centralizers to the pure one. The proved quadratic-subfield maximality
therefore applies to both ambient subgroups, even though a frame's chosen
comparison need not be induced by ambient conjugation. They are distinct:
otherwise their common center would contain the nontrivial linear twist,
contrary to the center-freeness of the fixed-field PGL₂ factor.

This proves the centralizer-pair join and supplies maximality for the four
normalizer joins in Aschbacher--Smith E.1.14(6), printed p.214 (Asc82a, 4.10).
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Geometry.Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

omit [Finite F] in
/-- All three elements in the frame's defining product are involutions,
so the linear twist commutes with the pure field involution. -/
theorem twist_mem_pureCentralizer (hσ : orderOf σ = 2) :
    c.z ∈ centralizer ({pure σ} : Set (innerModel F σ)) := by
  have hz : c.z * c.z = 1 := by
    simpa only [c.z_order, pow_two] using pow_orderOf_eq_one c.z
  have hs : pure σ * pure σ = 1 := by
    have h := pow_orderOf_eq_one (c.involution false)
    rw [c.involution_order hσ false] at h
    simpa only [involution, pow_two] using h
  have hzs : (c.z * pure σ) * (c.z * pure σ) = 1 := by
    simpa only [c.twist_order, pow_two] using pow_orderOf_eq_one (c.z * pure σ)
  rw [mem_centralizer_singleton_iff]
  calc
    c.z * pure σ = (c.z * pure σ)⁻¹ := (inv_eq_of_mul_eq_one_left hzs).symm
    _ = pure σ * c.z := by
      rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_left hs, inv_eq_of_mul_eq_one_left hz]

include hF hσ
variable [Finite (innerModel F σ)]

/-- Both literal centralizers are maximal subgroups of the inner model.
This uses an ambient conjugation, not the frame's abstract comparison. -/
theorem centralizer_isCoatom (i : Bool) : IsCoatom (c.centralizerAt i) := by
  have hmax := CentralizerPair.pureCentralizer_isCoatom
    (by decide : Nat.Prime 5) (by decide) hF σ hσ
  cases i
  · exact hmax
  · let : (innerModel F σ).Normal := CentralizerPair.innerModel_normal
      (by decide : Nat.Prime 5) (by decide) hF σ hσ
    have hr : ((c.z * pure σ : innerModel F σ) : PGammaL2 F).right = σ := by
      change (c.z : PGammaL2 F).right * σ = σ
      rw [c.z_linear, one_mul]
    have hne := ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
    obtain ⟨g, hg⟩ := projective_semilinear_involution_conj_inr
      (K := F) ⟨5, 2, by decide, by decide, by decide, hF⟩
      ((c.z * pure σ : innerModel F σ) : PGammaL2 F)
      ((Subgroup.orderOf_coe (c.z * pure σ)).trans c.twist_order)
      (by rw [hr]; exact hne)
    let a : MulAut (innerModel F σ) := MulAut.conjNormal (SemidirectProduct.inl g)⁻¹
    have ha : a (c.z * pure σ) = pure σ := by
      apply Subtype.ext
      change (SemidirectProduct.inl g)⁻¹ * ((c.z * pure σ : innerModel F σ) : PGammaL2 F) *
        ((SemidirectProduct.inl g)⁻¹)⁻¹ = SemidirectProduct.inr σ
      simpa only [inv_inv, hr] using hg
    have heq : c.centralizerAt true =
        (centralizer ({pure σ} : Set (innerModel F σ))).comap a.toMonoidHom := by
      ext x
      change x ∈ centralizer ({c.z * pure σ} : Set (innerModel F σ)) ↔
        a x ∈ centralizer ({pure σ} : Set (innerModel F σ))
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      constructor
      · intro h
        rw [← ha, ← map_mul, ← map_mul, h]
      · intro h
        apply a.injective
        simpa only [map_mul, ha] using h
    rw [heq]
    exact (Subgroup.isCoatom_comap a).mpr hmax

/-- The two centralizers of any actual frame generate the inner model. -/
theorem centralizer_pair_eq_top :
    c.centralizerAt false ⊔ c.centralizerAt true = ⊤ := by
  let C := c.centralizerAt false
  let D := c.centralizerAt true
  apply ((c.centralizer_isCoatom hF hσ false).ne_iff_eq_top le_sup_left).mp
  intro heq
  have hDC : D ≤ C := (le_sup_right : D ≤ C ⊔ D).trans_eq heq
  have hCD : C = D :=
    (eq_of_le_of_card_ge hDC (Nat.card_congr c.comparison.toEquiv).ge).symm
  have hzcomm : C ≤ centralizer ({c.z} : Set (innerModel F σ)) := by
    intro x hx
    have hc : x * pure σ = pure σ * x := mem_centralizer_singleton_iff.mp hx
    have hxD : x ∈ D := hCD ▸ hx
    have hd : x * (c.z * pure σ) = (c.z * pure σ) * x :=
      mem_centralizer_singleton_iff.mp hxD
    rw [mem_centralizer_singleton_iff]
    apply mul_right_cancel (b := pure σ)
    calc
      x * c.z * pure σ = x * (c.z * pure σ) := mul_assoc _ _ _
      _ = (c.z * pure σ) * x := hd
      _ = c.z * (x * pure σ) := by rw [mul_assoc, ← hc]
      _ = c.z * x * pure σ := (mul_assoc _ _ _).symm
  have hz1 := CentralizerPair.linear_central_eq_one
    (by decide : Nat.Prime 5) (by decide) hF σ hσ c.z
    (c.twist_mem_pureCentralizer hσ) c.z_linear hzcomm
  have hz := c.z_order
  simp [hz1] at hz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
