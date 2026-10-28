module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.F9
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.ElementaryAbelian.Quotient

/-!
# The original binary section in the nonabelian branch

The source U_H may be nonabelian. Its Frattini subgroup lies in the marked
point V₁, so the literal quotient U_H/V₁ is elementary abelian. F.9's exact
kernel equality gives a faithful action of H/O₂(H) on this quotient.
The original identity V₅ = V₁[U_H,V] then bounds every V-star displacement
by the four-dimensional image of V₅, with the quotient coordinates retained.

Source: Aschbacher--Smith, F.9.2 and opening of 12.6.26, pp.318,831--832.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

theorem point_normal_in_UH : (D.V₁.subgroupOf D.UH).Normal :=
  normal_subgroupOf_of_le_normalizer
    (h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))

theorem point_quotient_elementary :
    let := h.point_normal_in_UH
    IsElementaryAbelian 2 (D.UH ⧸ D.V₁.subgroupOf D.UH) := by
  let := h.point_normal_in_UH
  let : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
  let : IsElementaryAbelian 2 (D.UH ⧸ frattini D.UH) := isElementaryAbelian_quotient_frattini
  have hle : frattini D.UH ≤ (D.V₁.subgroupOf D.UH).comap (MonoidHom.id D.UH) := by
    intro u hu
    exact h.frattini_UH_le_point (mem_map_of_mem _ hu)
  exact IsElementaryAbelian.of_surjective
    (QuotientGroup.map (frattini D.UH) (D.V₁.subgroupOf D.UH) (MonoidHom.id _) hle)
    (QuotientGroup.map_surjective_of_surjective (frattini D.UH) (D.V₁.subgroupOf D.UH)
      (MonoidHom.id D.UH) (QuotientGroup.mk'_surjective _) hle)

/-- The faithful literal section, including when the original U_H is nonabelian. -/
theorem faithful_point_quotient :
    let := h.point_normal_in_UH
    let := h.point_quotient_elementary
    ∃ (σ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H)
        (Additive (D.UH ⧸ D.V₁.subgroupOf D.UH)))
      (c : BinaryConjugationSection D.H D.UH D.V₁
        (σ.comp (QuotientGroup.mk' (pCore 2 D.H)))),
      Function.Injective σ ∧
      ∀ u : D.UH, (c.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) := by
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  apply BinaryConjugationSection.exists_faithful_quotient_actor
    D.H D.UH D.V₁ h.UH_le_H (h.point_lt.le.trans (le_conjugateSpanBy _ _))
    (le_normalizer_conjugateSpanBy _ _) (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    (QuotientGroup.mk' (pCore 2 D.H)) (QuotientGroup.mk'_surjective _)
  intro a
  rw [←MonoidHom.mem_ker,QuotientGroup.ker_mk']
  have ha : a ∈ pCore 2 D.H ↔ (a : G) ∈ h.kernel D.UH := by
    rw [h.kernel_UH_eq_QH]
    change a ∈ pCore 2 D.H ↔ (a : G) ∈ (pCore 2 D.H).map D.H.subtype
    exact (mem_map_iff_mem (f := D.H.subtype) D.H.subtype_injective).symm
  rw [ha,h.mem_kernel_iff h.UH_le_H,and_iff_right a.property]
  constructor
  · intro hh u hu
    simpa only [commutatorElement_inv] using D.V₁.inv_mem (hh u hu)
  · intro hh u hu
    simpa only [commutatorElement_inv] using D.V₁.inv_mem (hh u hu)
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original star actor moves at most four dimensions on its literal faithful section. -/
theorem SourceHypothesis.original_binary_displacement_bound
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (c : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    ∀ v ∈ Nonabelian.Setup.star H V,
      Module.finrank (ZMod 2) (σ v - LinearMap.id).range ≤ 4 := by
  let E := D.fullSetup hZ T z
  have hg := S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn
  have hcomm : ⁅V,E.UH H⁆ ≤ E.V₅ := by
    rw [commutator_comm]
    exact le_sup_right.trans_eq hg.2.2.2.1.symm
  have hidx : E.V₁.relIndex E.V₅ = 2 ^ 4 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (E.V₁.subgroupOf E.V₅)
    rw [Nat.card_congr (subgroupOfEquivOfLe E.V₁_le_V₅).toEquiv] at hh
    change Nat.card E.V₅ = E.V₁.relIndex E.V₅ * Nat.card E.V₁ at hh
    rw [E.perpendicular_card hz,E.point_card hz] at hh
    omega
  have hd := c.imageSpace_finrank_of_index E.V₅ (le_conjugateSpanBy _ _) 4 hidx
  rintro v ⟨u,hu,rfl⟩
  have hl := c.displacement_range_le_imageSpace_of_commutator_le V E.V₅ hcomm u hu
  exact (Submodule.finrank_mono hl).trans hd.le
end CFSG.Quasithin.Chapter12.Section06
