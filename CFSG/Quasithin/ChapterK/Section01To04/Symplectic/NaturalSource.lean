module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Natural
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The natural parabolic actor in the original Chapter K group

Transport the literal plane radical along the group and module maps of a
natural identification, then along the actual component inclusion. Its
rank, fixed codimension, quadraticity and strict offender inequality are
preserved. Thus the original ambient representation has q at most 2/3.
Recognition of the natural identification is not asserted by this adapter.

Source: Aschbacher–Smith, K.3.4.1, printed p.456.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic
open scoped ENNReal
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair

variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The source parabolic actor, inside the original component and ambient action. -/
theorem natural_actor {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r)
    (h : NaturalIdentification (F := F) (ρ.comp L.subtype)) :
    ∃ A : Subgroup G, A ≤ L ∧ IsElementaryTwo A ∧ IsQuadratic ρ A ∧
      rank A = 3 * r ∧ fixedCodim ρ A = 2 * r ∧
      actionRatio ρ A = (2 : ℝ≥0∞) / 3 ∧ IsStrongOffender ρ A := by
  let f : Sp F →* G := L.subtype.comp h.groupEquiv.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp h.groupEquiv.symm.injective
  have hE (g : Sp F) (v : Vector F) :
      h.linearEquiv.symm (binaryNatural g v) = ρ (f g) (h.linearEquiv.symm v) := by
    apply h.linearEquiv.injective
    rw [h.linearEquiv.apply_symm_apply]
    have hh := h.intertwines (h.groupEquiv.symm g) (h.linearEquiv.symm v)
    change symplecticNatural 2 g v =
      h.linearEquiv ((ρ.comp L.subtype) (h.groupEquiv.symm g) (h.linearEquiv.symm v))
    simpa only [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] using hh.symm
  let A := planeRadical.map f
  have helem : IsElementaryTwo A := by
    let : IsElementaryAbelian 2 (planeRadical (F := F)) := planeRadical_elementary
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hz
    apply (Natural.planeRadical_isElementaryTwo hF hr).1
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hz
  have hquad : IsQuadratic ρ A := by
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
    obtain ⟨w, rfl⟩ := h.linearEquiv.symm.surjective v
    rw [← hE, ← map_sub, ← hE]
    exact congrArg h.linearEquiv.symm (Natural.planeRadical_quadratic x hx y hy w)
  have hrank : rank A = 3 * r := by
    rw [rank_map_injective f hf, rank_planeRadical hF]
  have hcodim : fixedCodim ρ A = 2 * r := by
    rw [← fixedCodim_map_equivariant binaryNatural ρ f h.linearEquiv.symm hE,
      planeRadical_natural_fixedCodim hF]
  have hratio : actionRatio ρ A = (2 : ℝ≥0∞) / 3 := by
    rw [← Natural.planeRadical_ratio hF hr]
    unfold actionRatio
    rw [hrank, hcodim, rank_planeRadical hF, planeRadical_natural_fixedCodim hF]
  refine ⟨A, ?_, helem, hquad, hrank, hcodim, hratio, helem, ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    exact (h.groupEquiv.symm g).property
  · rw [hrank, hcodim]
    omega

/-- Application of the concrete parabolic calculation to q(G,V), with an actual
natural-module identification as the sole representation-recognition premise. -/
theorem natural_quadraticRatio_le {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r)
    (h : NaturalIdentification (F := F) (ρ.comp L.subtype)) :
    quadraticRatio ρ ≤ (2 : ℝ≥0∞) / 3 := by
  obtain ⟨A, _, hA, hq, _, _, heq, _⟩ := natural_actor ρ L hF hr h
  rw [← heq]
  exact iInf_le_of_le A (iInf_le_of_le ⟨hA, hq⟩ le_rfl)

end CFSG.Quasithin.ChapterK.Symplectic
