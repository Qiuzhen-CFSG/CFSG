module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Normalizers of a self-centralizing dihedral pair

An element normalizing two commuting D₆ factors belongs to their join
when the centralizer of the join is contained in that join: every
D₆ automorphism is inner, and the remaining simultaneous centralizer
is absorbed. For D₁₀ an outer automorphism sends a marked rotation to
its square or cube. These finite rotation calculations are kernel checked.

The actual source consumer is the nonsingleton ratio decomposition in
`CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility`, for
Aschbacher--Smith 14.6.12(2), printed p.1031. The quintic conclusion is
an obstruction reduction, not an exclusion of the outer automorphism.
-/

public section
namespace DihedralGroup

private theorem aut_ext_generators {n : ℕ} [NeZero n] (a b : MulAut (DihedralGroup n))
    (hr : a (r 1) = b (r 1)) (hs : a (sr 0) = b (sr 0)) : a = b := by
  ext x
  have hrot (i : ZMod n) : a (r i) = b (r i) := by
    have he : (r i : DihedralGroup n) = (r 1) ^ i.val := by
      rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [he, map_pow, map_pow, hr]
  cases x with
  | r i => exact hrot i
  | sr i =>
    have he : (sr i : DihedralGroup n) = sr 0 * r i := by simp
    rw [he, map_mul, map_mul, hs, hrot]

private theorem aut_three_inner (a : MulAut (DihedralGroup 3)) :
    ∃ d : DihedralGroup 3, a = MulAut.conj d := by
  have hc : ∀ x y : DihedralGroup 3,
      x ^ 3 = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 →
      ∃ d : DihedralGroup 3, MulAut.conj d (r 1) = x ∧
        MulAut.conj d (sr 0) = y := by decide +kernel
  obtain ⟨d, hr, hs⟩ := hc (a (r 1)) (a (sr 0))
    (by rw [← map_pow, show (r 1 : DihedralGroup 3)^3 = 1 by decide, map_one])
    (a.map_ne_one_iff.mpr (by decide))
    (by rw [← map_pow]; simp [pow_two])
    (a.map_ne_one_iff.mpr (by decide))
  exact ⟨d, aut_ext_generators a (MulAut.conj d) hr.symm hs.symm⟩

private theorem aut_five_inner_of_rotation (a : MulAut (DihedralGroup 5))
    (hr : a (r 1) = r 1 ∨ a (r 1) = (r 1)⁻¹) :
    ∃ d : DihedralGroup 5, a = MulAut.conj d := by
  have hc : ∀ x y : DihedralGroup 5,
      (x = r 1 ∨ x = (r 1)⁻¹) → y ^ 2 = 1 → y ≠ 1 →
      ∃ d : DihedralGroup 5, MulAut.conj d (r 1) = x ∧
        MulAut.conj d (sr 0) = y := by decide +kernel
  obtain ⟨d, hr, hs⟩ := hc (a (r 1)) (a (sr 0)) hr
    (by rw [← map_pow]; simp [pow_two])
    (a.map_ne_one_iff.mpr (by decide))
  exact ⟨d, aut_ext_generators a (MulAut.conj d) hr.symm hs.symm⟩


private theorem outer_five_rotation (a : MulAut (DihedralGroup 5))
    (houter : ¬ ∃ d : DihedralGroup 5, a = MulAut.conj d) :
    a (r 1) = r 2 ∨ a (r 1) = r 3 := by
  have hnot : ¬ (a (r 1) = r 1 ∨ a (r 1) = (r 1)⁻¹) :=
    fun h => houter (aut_five_inner_of_rotation a h)
  have hc : ∀ x : DihedralGroup 5, x^5 = 1 → x ≠ 1 →
      ¬ (x = r 1 ∨ x = (r 1)⁻¹) → x = r 2 ∨ x = r 3 := by decide +kernel
  apply hc _ _ (a.map_ne_one_iff.mpr (by decide)) hnot
  rw [← map_pow, show (r 1 : DihedralGroup 5)^5 = 1 by decide, map_one]

end DihedralGroup

namespace Subgroup
variable {G : Type*} [Group G]

theorem mem_join_of_inner_on_commuting_factors (A B : Subgroup G)
    (hcom : ∀ x ∈ A, ∀ y ∈ B, Commute x y)
    (hcentral : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ A ⊔ B)
    (g : G)
    (hA : ∃ a : A, ∀ x : A, g * x * g⁻¹ = (a : G) * x * (a : G)⁻¹)
    (hB : ∃ b : B, ∀ x : B, g * x * g⁻¹ = (b : G) * x * (b : G)⁻¹) :
    g ∈ A ⊔ B := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  let c : G := (a : G) * b
  have hc : c ∈ A ⊔ B := (A ⊔ B).mul_mem ((le_sup_left : A ≤ A ⊔ B) a.property) ((le_sup_right : B ≤ A ⊔ B) b.property)
  have hfixA (x : A) : g * x * g⁻¹ = c * x * c⁻¹ := by
    rw [ha]
    have h := (hcom x x.property b b.property).eq
    dsimp [c]
    rw [mul_inv_rev, mul_assoc (a : G) (b : G) (x : G), ← h]
    group
  have hfixB (x : B) : g * x * g⁻¹ = c * x * c⁻¹ := by
    rw [hb]
    have h := (hcom a a.property x x.property).eq
    have hab := (hcom a a.property b b.property).eq
    dsimp [c]
    rw [hab, mul_inv_rev, mul_assoc (b : G) (a : G) (x : G), h]
    group
  have hz : c⁻¹ * g ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    have hle : A ⊔ B ≤ centralizer ({c⁻¹ * g} : Set G) := by
      apply sup_le
      · intro x hx
        apply mem_centralizer_singleton_iff.mpr
        have he' := congrArg (fun v : G => c⁻¹ * v * g) (hfixA ⟨x,hx⟩)
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
          mul_inv_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one, Subgroup.coe_mk] using he'.symm
      · intro x hx
        apply mem_centralizer_singleton_iff.mpr
        have he' := congrArg (fun v : G => c⁻¹ * v * g) (hfixB ⟨x,hx⟩)
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
          mul_inv_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one, Subgroup.coe_mk] using he'.symm
    exact fun x hx => (mem_centralizer_singleton_iff.mp (hle hx))
  have hg := (A ⊔ B).mul_mem hc (hcentral hz)
  simpa only [mul_inv_cancel_left] using hg


private theorem inner_on_dihedral_three (A : Subgroup G) (e : A ≃* DihedralGroup 3)
    (g : G) (hg : g ∈ normalizer (A : Set G)) :
    ∃ a : A, ∀ x : A, g * x * g⁻¹ = (a : G) * x * (a : G)⁻¹ := by
  let α : MulAut (DihedralGroup 3) :=
    (e.symm.trans (A.normalizerMonoidHom ⟨g,hg⟩)).trans e
  obtain ⟨b,hb⟩ := DihedralGroup.aut_three_inner α
  refine ⟨e.symm b, fun x => ?_⟩
  have he := congrArg (fun β : MulAut (DihedralGroup 3) => e.symm (β (e x))) hb
  have he' : A.normalizerMonoidHom ⟨g,hg⟩ x = e.symm b * x * (e.symm b)⁻¹ := by
    simpa only [α, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
      map_mul, map_inv] using he
  exact congrArg (fun x : A => (x : G)) he'


theorem normalizer_intersection_le_join_dihedral_three
    (A B : Subgroup G) (eA : A ≃* DihedralGroup 3) (eB : B ≃* DihedralGroup 3)
    (hcom : ∀ x ∈ A, ∀ y ∈ B, Commute x y)
    (hcentral : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ A ⊔ B) :
    normalizer (A : Set G) ⊓ normalizer (B : Set G) ≤ A ⊔ B := by
  intro g hg
  exact mem_join_of_inner_on_commuting_factors A B hcom hcentral g
    (inner_on_dihedral_three A eA g hg.1) (inner_on_dihedral_three B eB g hg.2)

theorem outer_on_dihedral_five_rotation (A : Subgroup G) (e : A ≃* DihedralGroup 5)
    (g : G) (hg : g ∈ normalizer (A : Set G))
    (houter : ¬ ∃ a : A, ∀ x : A, g * x * g⁻¹ = (a : G) * x * (a : G)⁻¹) :
    g * (e.symm (DihedralGroup.r 1) : G) * g⁻¹ = (e.symm (DihedralGroup.r 1) : G)^2 ∨
    g * (e.symm (DihedralGroup.r 1) : G) * g⁻¹ = (e.symm (DihedralGroup.r 1) : G)^3 := by
  let α : MulAut (DihedralGroup 5) :=
    (e.symm.trans (A.normalizerMonoidHom ⟨g,hg⟩)).trans e
  have ho : ¬ ∃ b : DihedralGroup 5, α = MulAut.conj b := by
    rintro ⟨b,hb⟩
    apply houter
    refine ⟨e.symm b, fun x => ?_⟩
    have he := congrArg (fun β : MulAut (DihedralGroup 5) => e.symm (β (e x))) hb
    have he' : A.normalizerMonoidHom ⟨g,hg⟩ x = e.symm b * x * (e.symm b)⁻¹ := by
      simpa only [α, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
        map_mul, map_inv] using he
    exact congrArg (fun x : A => (x : G)) he'
  have htransport (n : ℕ) (hn : α (DihedralGroup.r 1) = DihedralGroup.r (n : ZMod 5)) :
      g * (e.symm (DihedralGroup.r 1) : G) * g⁻¹ = (e.symm (DihedralGroup.r 1) : G)^n := by
    have he := congrArg e.symm hn
    have he' : A.normalizerMonoidHom ⟨g,hg⟩ (e.symm (DihedralGroup.r 1)) =
        (e.symm (DihedralGroup.r 1))^n := by
      simpa only [α, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        ← DihedralGroup.r_one_pow, map_pow] using he
    exact congrArg (fun x : A => (x : G)) he'
  rcases DihedralGroup.outer_five_rotation α ho with h | h
  · exact Or.inl (htransport 2 h)
  · exact Or.inr (htransport 3 h)

end Subgroup
