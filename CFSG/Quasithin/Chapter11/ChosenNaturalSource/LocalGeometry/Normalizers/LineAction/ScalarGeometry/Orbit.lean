module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.Representation.G2NaturalTransitivity

/-!
# Fusion of the original fixed line by the inner Sylow normalizer

The supplied full SL₃, Sp₄ and octonion G₂ actions are transitive on
nonzero vectors. If both endpoints are fixed by the inner Sylow, Sylow
conjugacy in the point stabilizer replaces any transporter by a normalizer
element. The quotient marking then gives a transporter in the literal
N_L(T_L), retaining the entire SL₃ center.

The preceding-source identity V₁ = C_V(T_L) is explicit; its producer is
`qt-d-1222-natural-flag-cartan`. No scalar, Singer or regularity premise is
assumed. Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Chapter 11 setup and 11.2.3, printed pp.759--761,768--769.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative Pointwise
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers

private theorem normalizer_transporter {H W : Type*} [Group H] [Finite H]
    [MulAction H W] (P : Sylow 2 H) (x y : W)
    (hx : ∀ p ∈ (P : Subgroup H), p • x = x)
    (hy : ∀ p ∈ (P : Subgroup H), p • y = y)
    (g : H) (hg : g • x = y) :
    ∃ n ∈ normalizer (P : Set H), n • x = y := by
  let C := MulAction.stabilizer H y
  have hP : (P : Subgroup H) ≤ C := hy
  have hQ : (g • P : Sylow 2 H) ≤ C := by
    rintro _ ⟨p,hp,rfl⟩
    change (g * p * g⁻¹) • y = y
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hx p hp]
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq C ((g • P).subtype hQ) (P.subtype hP)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
  exact ⟨h * g, Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh), by
    rw [mul_smul, hg]
    exact h.property⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

/-- Nonzero-vector transitivity for the actual full model in each coordinate row. -/
theorem model_transitive (c : Coordinates D F) (x y : c.Space) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : c.ModelGroup, c.modelAction g x = y := by
  cases c with
  | sl3 m => exact Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx hy
  | sp4 m => exact Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive hx hy
  | g2 m => exact Atlas.G2.Natural.action_transitive hx hy

/-- Nonzero vectors of the source fixed line are fused by the literal Cartan normalizer. -/
theorem normalizer_line_transitive
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (x y : f.space 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ n : cartanNormalizer T L,
      c.modelAction (c.quotientMap ⟨n,n.property.1⟩) x.val = y.val := by
  let ρ := c.modelAction.comp c.quotientMap
  let : MulAction L c.Space :=
    { smul := fun l v => ρ l v
      one_smul := by intro v; change ρ 1 v = v; simp
      mul_smul := by intro a b v; change ρ (a*b) v = ρ a (ρ b v); rw [map_mul]; rfl }
  have hfix (v : f.space 0) (p : L) (hp : p ∈ (c.innerSylow : Subgroup L)) : p • v.val = v.val := by
    obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v.val)
    have hwU : w.val ∈ f.Vi 0 := (c.mem_preimage _ w).mpr (by
      change (c.projection w).toAdd ∈ f.space 0
      rw [hw]
      exact v.property)
    have hpT : p.val ∈ T := by rw [c.innerSylow_coe] at hp; exact hp
    have hc := (hfixed ▸ hwU : w.val ∈ V ⊓ centralizer (sourceTL T L : Set G)).2
      p.val (sylow_intersection_le_sourceTL ⟨hpT,p.property⟩)
    have hconj : V.normalizerMonoidHom (inclusion D.normalizes p) w = w := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr hc
    change c.modelAction (c.quotientMap p) v.val = v.val
    rw [← show (c.projection w).toAdd = v.val from congrArg Multiplicative.toAdd hw,
      ← c.projection_component_conjugation, hconj]
  obtain ⟨g,hg⟩ := model_transitive c x.val y.val
    (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
  obtain ⟨l,hl⟩ := c.quotientMap_surjective g
  obtain ⟨n,hn,he⟩ := normalizer_transporter c.innerSylow x.val y.val
    (hfix x) (hfix y) l (by change c.modelAction (c.quotientMap l) x.val = y.val; rw [hl]; exact hg)
  have hN : n.val ∈ cartanNormalizer T L := by
    rw [← componentNormalizer_map c.innerSylow c.innerSylow_coe]
    exact mem_map_of_mem _ hn
  exact ⟨⟨n,hN⟩,he⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
