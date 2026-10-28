module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Geometry.Action
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Lifting point-residual generation through the actual two-core

The marked action maps the actual relative flag normalizers onto the
linear parabolics, and maps their two-residuals onto the corresponding
linear residuals. A conjugate span with full linear image supplements
O₂(L). Since the core lies in its acting subgroup, that span is normal
in L; O²(L)=L then removes the two-group quotient.

The concrete linear generation is still an explicit premise of
`flag_generation_of_linear`. The n=5 exceptional solvable residuals of
L₂ and L₃ are not used or changed: L₁ always uses the two-residual.

Source: Aschbacher–Smith, Lemma 12.8.5(2), printed p.850 (PDF p.867).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.NormalGeometry
variable {G D : Type*} [Group G] [Group D]

private theorem span_eq_top_of_image (p : ℕ) (f : G →* D) (A P : Subgroup G)
    (hG : pResidual p G = ⊤) (hk : IsPGroup p f.ker) (hkP : f.ker ≤ P)
    (him : conjugateSpanBy (A.map f) (P.map f) = ⊤) :
    conjugateSpanBy A P = ⊤ := by
  let S := conjugateSpanBy A P
  have hsmap : S.map f = ⊤ := by rw [map_conjugateSpanBy, him]
  have hs : S ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hsmap, comap_top]
  have hnormal : S.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hs]
    exact sup_le S.le_normalizer (hkP.trans (le_normalizer_conjugateSpanBy A P))
  let := hnormal
  have hquot := isPGroup_quotient_of_sup_eq_top S f.ker hk hs
  exact top_unique (hG ▸ (show pResidual p G ≤ S from sInf_le ⟨hnormal, hquot⟩))

end CFSG.Quasithin.Chapter12.Section08.NormalGeometry

namespace CFSG.Quasithin.Chapter12.Section08.NormalGeometry
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {V L : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- The exact image of the relative flag stabilizer. -/
theorem flag_parabolic_image (F : InvariantFlag T V n) (d : NaturalAction L V) (i : ℕ) :
    ((L ⊓ F.Gi i).subgroupOf L).map d.action =
      BinaryLinear.parabolic (space (V := V) (F.Vi i)) := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (action_mem_parabolic_iff d _ (F.le_seed i) l).mpr hl.2
  · intro ha
    obtain ⟨l, rfl⟩ := d.surjective a
    exact ⟨l, ⟨l.property, (action_mem_parabolic_iff d _ (F.le_seed i) l).mp ha⟩, rfl⟩

omit [IsElementaryAbelian 2 V] in
private theorem intrinsic_point_residual (F : InvariantFlag T V n) :
    ((pResidual 2 ((L ⊓ F.Gi 1).subgroupOf L)).map
      ((L ⊓ F.Gi 1).subgroupOf L).subtype).map L.subtype = F.Li L 1 := by
  rw [map_embedded_pResidual, map_subgroupOf_eq_of_le (show L ⊓ F.Gi 1 ≤ L from inf_le_left)]
  simp only [InvariantFlag.Li, show ¬(n = 5 ∧ (1 = 2 ∨ 1 = 3)) by omega, ↓reduceIte]

/-- Lift the concrete linear generation through the genuine two-core of L.
The point residual is O²; the exceptional solvable residuals at n=5,i=2,3
are untouched. The remaining linear calculation is the explicit premise. -/
theorem flag_generation_of_linear (F : InvariantFlag T V n) (d : NaturalAction L V)
    (hL : pResidual 2 L = ⊤) (i : ℕ)
    (hlinear : conjugateSpanBy
      ((pResidual 2 (BinaryLinear.parabolic (space (V := V) (F.Vi 1)))).map
        (BinaryLinear.parabolic (space (V := V) (F.Vi 1))).subtype)
      (BinaryLinear.parabolic (space (V := V) (F.Vi i))) = ⊤) :
    conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L := by
  let P₁ := (L ⊓ F.Gi 1).subgroupOf L
  let Pᵢ := (L ⊓ F.Gi i).subgroupOf L
  let A := (pResidual 2 P₁).map P₁.subtype
  have hker : d.action.ker ≤ Pᵢ := by
    intro l hl
    refine ⟨l.property, (action_mem_parabolic_iff d _ (F.le_seed i) l).mp ?_⟩
    rw [show d.action l = 1 from hl]
    exact one_mem _
  have hA : A.map d.action =
      (pResidual 2 (BinaryLinear.parabolic (space (V := V) (F.Vi 1)))).map
        (BinaryLinear.parabolic (space (V := V) (F.Vi 1))).subtype := by
    dsimp [A, P₁]
    rw [map_embedded_pResidual, flag_parabolic_image F d 1]
  have hgen : conjugateSpanBy A Pᵢ = ⊤ :=
    span_eq_top_of_image 2 d.action A Pᵢ hL
      (by rw [d.kernel]; exact pCore_isPGroup) hker (by
        rw [hA, show Pᵢ.map d.action = _ from flag_parabolic_image F d i]
        exact hlinear)
  have h := congrArg (fun S : Subgroup L => S.map L.subtype) hgen
  rw [map_conjugateSpanBy, intrinsic_point_residual F,
    map_subgroupOf_eq_of_le (show L ⊓ F.Gi i ≤ L from inf_le_left),
    ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

end CFSG.Quasithin.Chapter12.Section08.NormalGeometry

