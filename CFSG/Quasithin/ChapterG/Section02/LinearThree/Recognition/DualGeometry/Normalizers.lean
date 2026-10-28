module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Models
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Normalization by the genuine point stabilizers in G.2.5

Restrict the given Sylow subgroup first to L and then to N_L(V₁). Its
supplement by O²(N_L(V₁)) places the full point normalizer inside H.
Since T fixes V₁, the same containment holds for N_LT(V₁). The H-closure
U is therefore normalized by these actors. Conjugating proves the precise
normalization of Uᵍ and Uʰ used in the root-group argument.

This uses O² only for the source definition of L₁. The distinct plane
stabilizer residual in G.2.5 is O^{2′} and is not identified here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis G.2.1 and proof of G.2.5(6), printed pp.332,335–336.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d

/-- The full point normalizer lies in the original local overgroup H.
The two-residual and the original Sylow subgroup together cover it. -/
theorem pointNormalizer_le_H : D.L ⊓ D.G₁ ≤ D.H := by
  let N := D.L.subgroupOf D.LT
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  let e : N ≃* D.L := subgroupOfEquivOfLe (show D.L ≤ D.LT from le_sup_left)
  let R : Sylow 2 D.L := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRT : (R : Subgroup D.L).map D.L.subtype ≤ D.T := by
    rintro _ ⟨l, hl, rfl⟩
    change l ∈ (Q : Subgroup N).map e.toMonoidHom at hl
    obtain ⟨q, hq, rfl⟩ := hl
    have hqp : (q : D.LT) ∈ P := by
      rw [hQ] at hq
      exact hq
    rw [← hP]
    exact ⟨q.val, hqp, rfl⟩
  let A := D.L ⊓ D.G₁
  let B := A.subgroupOf D.L
  have hRB : (R : Subgroup D.L) ≤ B := by
    intro l hl
    exact ⟨l.property, d.setup.T_normalizes_point (hRT (mem_map_of_mem D.L.subtype hl))⟩
  let RB : Sylow 2 B := R.subtype hRB
  let eB : B ≃* A := subgroupOfEquivOfLe (show A ≤ D.L from inf_le_left)
  let RA : Sylow 2 A := RB.mapSurjective (f := eB.toMonoidHom) eB.surjective
  have hRA : (RA : Subgroup A).map A.subtype ≤ D.T := by
    rintro _ ⟨a, ha, rfl⟩
    change a ∈ (RB : Subgroup B).map eB.toMonoidHom at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hbR : (b : D.L) ∈ R := hb
    exact hRT (mem_map_of_mem D.L.subtype hbR)
  have hs := congrArg (fun X : Subgroup A => X.map A.subtype)
    (pResidual_sup_sylow_eq_top RA)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  change A ≤ D.H
  rw [← hs]
  exact sup_le ((show (pResidual 2 A).map A.subtype = D.L₁ from rfl).le.trans
    (le_sup_left.trans d.setup.local_le)) (hRA.trans (le_sup_right.trans d.setup.local_le))

/-- The same containment holds in LT: the given T already fixes the point. -/
theorem pointNormalizerLT_le_H : D.LT ⊓ D.G₁ ≤ D.H := by
  intro x hx
  have hx' : x ∈ (D.L : Set G) * (D.T : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ d.setup.T_normalizes_L]
    exact hx.1
  obtain ⟨l, hl, t, ht, rfl⟩ := hx'
  have hlG : l ∈ D.G₁ := by
    have he := D.G₁.mul_mem hx.2 (D.G₁.inv_mem (d.setup.T_normalizes_point ht))
    simpa only [mul_inv_cancel_right] using he
  exact D.H.mul_mem (pointNormalizer_le_H d ⟨hl, hlG⟩)
    (d.setup.local_le (mem_sup_right ht))

/-- The full LT point stabilizer normalizes U before taking starred images. -/
theorem pointNormalizerLT_normalizes_U :
    D.LT ⊓ D.G₁ ≤ normalizer (D.U : Set G) :=
  (pointNormalizerLT_le_H d).trans (le_normalizer_conjugateSpanBy D.V D.H)

/-- Point-stabilizer normalization is proved for U itself, before taking stars. -/
theorem pointNormalizer_normalizes_U :
    D.L ⊓ D.G₁ ≤ normalizer (D.U : Set G) :=
  (pointNormalizer_le_H d).trans (le_normalizer_conjugateSpanBy D.V D.H)

/-- The source point-normalizer argument applies to each original conjugate,
with the same conjugator on its U-group. -/
theorem conjugatePointNormalizer_normalizes_U (x : D.L) :
    D.L ⊓ normalizer (Setup.conjugate D.V₁ (x : G) : Set G) ≤
      normalizer (Setup.conjugate D.U (x : G) : Set G) := by
  let f := (MulAut.conj (x : G)⁻¹).toMonoidHom
  have he : D.L.map f = D.L :=
    mem_normalizer_iff_map_conj_eq.mp (D.L.le_normalizer (D.L.inv_mem x.property))
  have hm := map_mono (f := f) (pointNormalizer_normalizes_U d)
  rw [Subgroup.map_inf _ _ f (MulAut.conj (x : G)⁻¹).injective, he,
    show D.G₁ = normalizer (D.V₁ : Set G) from rfl,
    map_normalizer_eq_of_bijective _ (MulAut.conj (x : G)⁻¹).bijective,
    map_normalizer_eq_of_bijective _ (MulAut.conj (x : G)⁻¹).bijective] at hm
  exact hm

/-- Normalization at a conjugate point holds for the full LT actor. -/
theorem conjugatePointNormalizerLT_normalizes_U (x : D.L) :
    D.LT ⊓ normalizer (Setup.conjugate D.V₁ (x : G) : Set G) ≤
      normalizer (Setup.conjugate D.U (x : G) : Set G) := by
  let f := (MulAut.conj (x : G)⁻¹).toMonoidHom
  have he : D.LT.map f = D.LT :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.LT.le_normalizer (D.LT.inv_mem (mem_sup_left x.property)))
  have hm := map_mono (f := f) (pointNormalizerLT_normalizes_U d)
  rw [Subgroup.map_inf _ _ f (MulAut.conj (x : G)⁻¹).injective, he,
    show D.G₁ = normalizer (D.V₁ : Set G) from rfl,
    map_normalizer_eq_of_bijective _ (MulAut.conj (x : G)⁻¹).bijective,
    map_normalizer_eq_of_bijective _ (MulAut.conj (x : G)⁻¹).bijective] at hm
  exact hm

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
