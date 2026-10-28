module
public import CFSG.Quasithin.ChapterF.Section09.F7Specialization
public import Theory.GroupTheory.ConjugationLocalGeometry

/-!
# Conjugate intersections in F.9.6

The point-normalizer equality from F.9.2(4) makes the conjugates of each
H-invariant subgroup depend only on the displaced point, proving F.9.6(1).
The central commutator bound and disjointness of distinct order-two points
prove both assertions of F.9.6(3), without a square condition.

For F.9.6(2), `intersection_exchange_chosen` uses the specified representative
g₀ whose square lies in L₁T. `intersection_exchange_of_square` covers the
source's subsequent application, where g itself was chosen with this property.
Neither result asserts the printed exchange by an arbitrary original g:
changing to g₀ preserves the named subgroup conjugates but not the conjugating
element applied to their intersections. `intersection_conjugate_formula`
records the exact remaining Q_H^(g²) factor. The computational diagnostic in
`Intersections/source/README.md` exhibits the issue under the original F.9.1
hypotheses; it is not imported or used as a Lean proof.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.6,
printed pp.320–321; the square-stabilizing application is on printed p.941.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section09.Setup
variable {G : Type*} [Group G]

/-- Right conjugation, as in the source. -/
abbrev conjugate (A : Subgroup G) (g : G) : Subgroup G :=
  ChapterG.Section02.Setup.conjugate A g

def DH (D : Setup G) (g : G) : Subgroup G := D.UH ⊓ conjugate D.QH g
def DHg (D : Setup G) (g : G) : Subgroup G := conjugate D.UH g ⊓ D.QH
def EH (D : Setup G) (g : G) : Subgroup G := D.VH ⊓ conjugate D.QH g
def EHg (D : Setup G) (g : G) : Subgroup G := conjugate D.VH g ⊓ D.QH

private theorem conjugate_mul (A : Subgroup G) (g y : G) :
    conjugate A (g * y) = conjugate (conjugate A g) y := by
  unfold conjugate ChapterG.Section02.Setup.conjugate
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]

private theorem conjugate_one (A : Subgroup G) : conjugate A 1 = A := by
  change A.map (MulAut.conj (1 : G)⁻¹).toMonoidHom = A
  simp only [inv_one, map_one]
  exact map_id A

private theorem conjugate_inf (A B : Subgroup G) (g : G) :
    conjugate (A ⊓ B) g = conjugate A g ⊓ conjugate B g :=
  Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

private theorem conjugate_eq_self {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) : conjugate A g = A :=
  mem_normalizer_iff_map_conj_eq.mp ((normalizer (A : Set G)).inv_mem hg)

variable [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h

/-- The conjugate of any H-invariant subgroup depends only on the displaced point. -/
theorem conjugate_eq_of_point_eq (X : Subgroup G)
    (hX : D.H ≤ normalizer (X : Set G)) {g y : G}
    (hg : g ∈ D.LT) (hy : y ∈ D.LT)
    (he : conjugate D.V₁ g = conjugate D.V₁ y) :
    conjugate X g = conjugate X y := by
  have hn : g * y⁻¹ ∈ normalizer (D.V₁ : Set G) := by
    have he' : conjugate D.V₁ (g * y⁻¹) = D.V₁ := by
      rw [conjugate_mul, he, ← conjugate_mul, mul_inv_cancel, conjugate_one]
    simpa only [inv_inv] using (normalizer (D.V₁ : Set G)).inv_mem
      (mem_normalizer_iff_map_conj_eq.mpr he')
  have hnH : g * y⁻¹ ∈ D.H :=
    h.local_le (h.normalizer_point_LT_eq ▸ ⟨D.LT.mul_mem hg (D.LT.inv_mem hy), hn⟩)
  have heX := conjugate_eq_self (hX hnH)
  have hh := congrArg (fun A => conjugate A y) heX
  rwa [← conjugate_mul, inv_mul_cancel_right] at hh

/-- F.9.6(1), including y in LT rather than just in L. -/
theorem lemma_F_9_6_one {g y : G} (hg : g ∈ D.L) (hy : y ∈ D.LT)
    (he : conjugate D.V₁ g = conjugate D.V₁ y) :
    conjugate D.H g = conjugate D.H y ∧
    conjugate D.QH g = conjugate D.QH y ∧
    conjugate D.UH g = conjugate D.UH y ∧
    conjugate D.VH g = conjugate D.VH y :=
  ⟨h.conjugate_eq_of_point_eq D.H D.H.le_normalizer (mem_sup_left hg) hy he,
    h.conjugate_eq_of_point_eq D.QH H_normalizes_QH (mem_sup_left hg) hy he,
    h.conjugate_eq_of_point_eq D.UH (le_normalizer_conjugateSpanBy _ _)
      (mem_sup_left hg) hy he,
    h.conjugate_eq_of_point_eq D.VH (le_normalizer_conjugateSpanBy _ _)
      (mem_sup_left hg) hy he⟩

omit [Finite G] h in
/-- For an arbitrary representative the second intersection factor is Q_H^(g²).
Equality of the displaced point with that of some other representative does not
itself remove this factor. -/
theorem intersection_conjugate_formula (g : G) :
    conjugate (D.DH g) g = conjugate D.UH g ⊓ conjugate D.QH (g ^ 2) ∧
    conjugate (D.EH g) g = conjugate D.VH g ⊓ conjugate D.QH (g ^ 2) := by
  constructor
  · rw [DH, conjugate_inf, ← conjugate_mul, pow_two]
  · rw [EH, conjugate_inf, ← conjugate_mul, pow_two]

/-- The intersection exchange for a representative whose square fixes the point. -/
theorem intersection_exchange_of_square {g : G}
    (hs : g ^ 2 ∈ D.L₁ ⊔ (D.T : Subgroup G)) :
    conjugate (D.DH g) g = D.DHg g ∧ conjugate (D.EH g) g = D.EHg g := by
  have hQ : conjugate (conjugate D.QH g) g = D.QH := by
    rw [← conjugate_mul, ← pow_two]
    exact conjugate_eq_self (H_normalizes_QH (h.local_le hs))
  constructor
  · rw [DH, DHg, conjugate_inf, hQ]
  · rw [EH, EHg, conjugate_inf, hQ]

/-- With a specified square-stabilizing representative g₀, its conjugation exchanges
both intersections attached to the same displaced point. -/
theorem intersection_exchange_chosen {g g₀ : G}
    (hg : g ∈ D.L) (hg₀ : g₀ ∈ D.L)
    (he : conjugate D.V₁ g = conjugate D.V₁ g₀)
    (hs : g₀ ^ 2 ∈ D.L₁ ⊔ (D.T : Subgroup G)) :
    conjugate (D.DH g) g₀ = D.DHg g ∧ conjugate (D.EH g) g₀ = D.EHg g := by
  obtain ⟨_, hQ, hU, hV⟩ := h.lemma_F_9_6_one hg (mem_sup_left hg₀) he
  have hd : D.DH g = D.DH g₀ := congrArg (D.UH ⊓ ·) hQ
  have hd' : D.DHg g = D.DHg g₀ := congrArg (· ⊓ D.QH) hU
  have heh : D.EH g = D.EH g₀ := congrArg (D.VH ⊓ ·) hQ
  have heh' : D.EHg g = D.EHg g₀ := congrArg (· ⊓ D.QH) hV
  rw [hd, hd', heh, heh']
  exact h.intersection_exchange_of_square hs

/-- The first commutator bound of F.9.6(3) does not require a square condition. -/
theorem commutator_EH_conjugate_UH (g : G) :
    ⁅D.EH g, conjugate D.UH g⁆ ≤ conjugate D.V₁ g := by
  have hc := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h.commutator_UH_QH_le_point
  rw [map_commutator, commutator_comm] at hc
  exact (commutator_mono inf_le_right le_rfl).trans hc

/-- F.9.6(3), retaining the two distinct intersections and the displaced order-two point. -/
theorem lemma_F_9_6_three {g : G} (hne : D.V₁ ≠ conjugate D.V₁ g) :
    ⁅D.EH g, conjugate D.UH g⁆ ≤ conjugate D.V₁ g ∧ ⁅D.DH g, D.DHg g⁆ = ⊥ := by
  refine ⟨h.commutator_EH_conjugate_UH g, ?_⟩
  have hD : D.DH g ≤ D.EH g :=
    inf_le_inf_right _ (conjugateSpanBy_mono h.plus_le le_rfl)
  have hc₁ : ⁅D.DH g, D.DHg g⁆ ≤ D.V₁ :=
    (commutator_mono inf_le_left inf_le_right).trans h.commutator_UH_QH_le_point
  have hc₂ : ⁅D.DH g, D.DHg g⁆ ≤ conjugate D.V₁ g :=
    (commutator_mono hD inf_le_left).trans (h.commutator_EH_conjugate_UH g)
  have hcard : Nat.card (conjugate D.V₁ g) = 2 := by
    exact (Nat.card_congr (D.V₁.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.toEquiv).trans h.point_card
  exact eq_bot_iff.mpr ((le_inf hc₁ hc₂).trans
    (inf_eq_bot_of_card_two_of_ne _ _ h.point_card hcard hne).le)

end Hypothesis
end CFSG.Quasithin.ChapterF.Section09.Setup
