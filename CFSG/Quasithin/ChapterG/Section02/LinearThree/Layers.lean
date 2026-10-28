module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Source

/-!
# The product defining the third term of G.2.5

Once L lies in I, its marked conjugators preserve S=O₂(I), so the triple
intersection of U is exactly the triple intersection of W. This gives
V≤S₂≤S₃≤S. Two of the pair intersections lie in a common conjugate of U;
their commutator is therefore in the corresponding marked point, hence
in V≤S₂. They normalize one another, identifying the join defining S₃
with the literal three-factor product in the source.

This proves the product identity without assuming that S₃ lies in W or
that S₃ is invariant under all of I. The latter is a separate root-action
step in the natural/dual recognition argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(4), printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
variable {G : Type*} [Group G]

theorem I_normalizes_core (D : Setup G) (g h : G) :
    I D g h ≤ normalizer (S D g h : Set G) := by
  have hm := (pCore 2 (I D g h)).le_normalizer_map (I D g h).subtype
  rw [normalizer_eq_top] at hm
  have ht : (⊤ : Subgroup (I D g h)).map (I D g h).subtype = I D g h := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, mem_top _, rfl⟩
  rw [ht] at hm
  exact hm

theorem conjugate_core (D : Setup G) (g h x : G) (hx : x ∈ I D g h) :
    conjugate (S D g h) x = S D g h :=
  mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (S D g h : Set G)).inv_mem (I_normalizes_core D g h hx))

/-- The marked conjugate Wˣ is the intersection Uˣ∩S for x∈I. -/
theorem conjugate_W (D : Setup G) (g h x : G) (hx : x ∈ I D g h) :
    conjugate (W D g h) x = conjugate D.U x ⊓ S D g h := by
  change (D.U ⊓ S D g h).map (MulAut.conj x⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj x⁻¹).injective]
  rw [show (S D g h).map (MulAut.conj x⁻¹).toMonoidHom = S D g h from
    conjugate_core D g h x hx]
  rfl

namespace Hypothesis
variable [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)
include d

/-- The denominator is literally the common intersection of the three
marked W-groups; only the previously proved intersection layer is used. -/
theorem S₂_eq_triple_W (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    S₂ D g h = (W D g h ⊓ conjugate (W D g h) g) ⊓ conjugate (W D g h) h := by
  rw [conjugate_W D g h g (hLI d.g_mem), conjugate_W D g h h (hLI d.h_mem)]
  have heS := (d.intersection hUT hf).2.1
  apply le_antisymm
  · intro x hx
    exact ⟨⟨⟨hx.1.1, heS hx⟩, ⟨hx.1.2, heS hx⟩⟩, ⟨hx.2, heS hx⟩⟩
  · intro x hx
    exact ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩

/-- All containments in the printed series, with relative I-normality of
S₃ left to the recognition argument. -/
theorem series_inclusions (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    D.V ≤ S₂ D g h ∧ S₂ D g h ≤ S₃ D g h ∧ S₃ D g h ≤ S D g h := by
  have heS₃ : S₂ D g h ≤ S₃ D g h := by
    rw [d.S₂_eq_triple_W hUT hf hLI]
    exact inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hgS : conjugate (W D g h) g ≤ S D g h := by
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact inf_le_right
  exact ⟨(d.intersection hUT hf).1, heS₃,
    sup_le (sup_le (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right))
      (inf_le_left.trans hgS)⟩

/-- The join used to define S₃ is exactly the source's ordered set product
of the three pair intersections, not just the subgroup they generate. -/
theorem S₃_product (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    (S₃ D g h : Set G) =
      ((W D g h ⊓ conjugate (W D g h) g : Subgroup G) : Set G) *
        ((W D g h ⊓ conjugate (W D g h) h : Subgroup G) : Set G) *
        ((conjugate (W D g h) g ⊓ conjugate (W D g h) h : Subgroup G) : Set G) := by
  let A := W D g h ⊓ conjugate (W D g h) g
  let B := W D g h ⊓ conjugate (W D g h) h
  let C := conjugate (W D g h) g ⊓ conjugate (W D g h) h
  have hEB : S₂ D g h ≤ B := by
    rw [d.S₂_eq_triple_W hUT hf hLI]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hEC : S₂ D g h ≤ C := by
    rw [d.S₂_eq_triple_W hUT hf hLI]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hVE := (d.intersection hUT hf).1
  have hder : ⁅D.U, D.U⁆ ≤ D.V :=
    (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans d.setup.point_le
  have hderc (x : G) (hx : x ∈ D.L) : ⁅conjugate D.U x, conjugate D.U x⁆ ≤ D.V := by
    have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hder
    rw [map_commutator] at hm
    have he : D.V.map (MulAut.conj x⁻¹).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.V : Set G)).inv_mem (normalizes_of_span D d.span_eq hx))
    exact hm.trans he.le
  have hWg : conjugate (W D g h) g ≤ conjugate D.U g := map_mono inf_le_left
  have hWh : conjugate (W D g h) h ≤ conjugate D.U h := map_mono inf_le_left
  have hAB : ⁅A, B⁆ ≤ D.V :=
    (commutator_mono (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_left)).trans hder
  have hAC : ⁅A, C⁆ ≤ D.V :=
    (commutator_mono (inf_le_right.trans hWg) (inf_le_left.trans hWg)).trans (hderc g d.g_mem)
  have hBC : ⁅B, C⁆ ≤ D.V :=
    (commutator_mono (inf_le_right.trans hWh) (inf_le_right.trans hWh)).trans (hderc h d.h_mem)
  have hnAB : A ≤ normalizer (B : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hAB.trans (hVE.trans hEB))
  have hnAC : A ≤ normalizer (C : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hAC.trans (hVE.trans hEC))
  have hnBC : B ≤ normalizer (C : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hBC.trans (hVE.trans hEC))
  change (((A ⊔ B) ⊔ C : Subgroup G) : Set G) = _
  rw [coe_mul_of_left_le_normalizer_right (A ⊔ B) C (sup_le hnAC hnBC),
    coe_mul_of_left_le_normalizer_right A B hnAB]

/-- The denominator induced on W is the product of its two pair
intersections. This is the precise intersection needed when computing
the order of the image W/S₃; it does not assert S₃≤W. -/
theorem W_inf_S₃ (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    W D g h ⊓ S₃ D g h =
      (W D g h ⊓ conjugate (W D g h) g) ⊔
        (W D g h ⊓ conjugate (W D g h) h) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈
        ((W D g h ⊓ conjugate (W D g h) g : Subgroup G) : Set G) *
          ((W D g h ⊓ conjugate (W D g h) h : Subgroup G) : Set G) *
          ((conjugate (W D g h) g ⊓ conjugate (W D g h) h : Subgroup G) : Set G) := by
      rw [← d.S₃_product hUT hf hLI]
      exact hx.2
    obtain ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hx'
    have hcW : c ∈ W D g h := by
      have hm := (W D g h).mul_mem
        ((W D g h).inv_mem ((W D g h).mul_mem ha.1 hb.1)) hx.1
      simpa only [inv_mul_cancel_left] using hm
    exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right hb))
      (mem_sup_left ⟨hcW, hc.1⟩)
  · exact le_inf (sup_le inf_le_left inf_le_left) le_sup_left

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
