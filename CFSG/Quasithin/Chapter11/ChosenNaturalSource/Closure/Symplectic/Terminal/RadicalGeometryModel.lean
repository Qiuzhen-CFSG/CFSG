module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# The intrinsic radical calculation for the last line of 11.5.7

The actual plane radical has no proper noncentral invariant subgroup. Its
commutator generation therefore makes every nonzero perfectly moved subgroup
the whole radical. The same statement is transported through any faithful
embedding. An explicit diagonal shear lies in the point local group but not
in its two-core; this is the separation needed by the original action-image
consumer in RadicalGeometry.

Source: Aschbacher--Smith, 11.5.7, printed p.784; the intrinsic plane results
are the matrix calculations of F.1.12(I)(2), printed pp.262--264.
-/

public noncomputable section
open Subgroup
open scoped Matrix
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometry
variable {F : Type*} [Field F]

abbrev planeRadical : Subgroup (Sp F) := Plane.radical.map planeLocal.subtype
abbrev pointRadical : Subgroup (Sp F) :=
  Theory.SpecificGroups.SymplecticFour.pointRadical.map pointLocal.subtype

theorem planeRadical_le_pointLocal : planeRadical (F := F) ≤ pointLocal := by
  rintro _ ⟨q,hq,rfl⟩
  apply (mem_pointLocal_iff_fixed q.val).mpr
  change q.val.val *ᵥ e 0 = e 0
  rw [Plane.radical_matrix ⟨q,hq⟩]
  ext i
  cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, Matrix.mulVec_single, Matrix.fromBlocks, Matrix.one_apply, Pi.single_apply]

theorem planeRadical_not_le_pointRadical :
    ¬ planeRadical (F := F) ≤ pointRadical := by
  let B : Plane.symmetricMatrices F := ⟨!![0,0;0,1], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  let q := Plane.shear B
  have hq : q.val ∈ planeRadical := mem_map_of_mem planeLocal.subtype (show q ∈ Plane.radical from Plane.quotientMap_shear B)
  intro h
  obtain ⟨p,hp,he⟩ := h hq
  have hp' : pointQuotient p = 1 := hp
  have hm := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 2) F => a.val 0 1) hp'
  have hv : p.val = q.val := he
  change p.val.val (.inl 1) (.inr 1) = 0 at hm
  rw [hv] at hm
  simp [q, Plane.shear, Plane.shearSp, B, Matrix.fromBlocks] at hm

variable {H : Type*} [Group H]

/-- Mutual normalization bounds the commutator by the local two-core. -/
theorem commutator_le_localCore (Q J : Subgroup H) (hQ : IsPGroup 2 Q)
    (hJQ : J ≤ normalizer (Q : Set H)) (hQJ : Q ≤ normalizer (J : Set H)) :
    ⁅Q,J⁆ ≤ J.pCoreIn 2 :=
  le_pCoreIn_of_normalizes
    (hQ.to_le (le_normalizer_iff_commutator_le_left.mp hJQ))
    (le_normalizer_iff_commutator_le_right.mp hQJ)
    (normalizer_commutator_ge_right Q J)

/-- A local normal two-subgroup intersects the local factor in its two-core. -/
theorem inf_le_localCore (Q J : Subgroup H) (hQ : IsPGroup 2 Q)
    (hJQ : J ≤ normalizer (Q : Set H)) : Q ⊓ J ≤ J.pCoreIn 2 :=
  le_pCoreIn_of_normalizes (hQ.to_le inf_le_left) inf_le_right
    ((le_inf hJQ J.le_normalizer).trans inf_normalizer_le_normalizer_inf)

variable [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
include hcard hn

/-- Perfect movement excludes the central alternative of the plane radical. -/
theorem plane_moved_eq (B : Subgroup (planeLocal (F := F)))
    (hB : B ≤ Plane.radical) (hm : ⁅B,⊤⁆ = B) (hne : B ≠ ⊥) :
    B = Plane.radical := by
  have hnormal : B.Normal := normalizer_eq_top_iff.mp
    (top_unique (le_normalizer_iff_commutator_le_left.mpr hm.le))
  let := hnormal
  rcases Plane.normal_radical_le_center_or_eq hcard hn B hB with hc | he
  · apply (hne ?_).elim
    rw [← hm, commutator_eq_bot_iff_le_centralizer]
    simpa only [Subgroup.coe_top, centralizer_univ] using hc
  · exact he

/-- The same calculation under a faithful embedding into the actual action group. -/
theorem plane_moved_image (j : planeLocal (F := F) →* H) (hj : Function.Injective j)
    (B : Subgroup H) (hB : B ≤ Plane.radical.map j)
    (hm : ⁅B,j.range⁆ = B) (hne : B ≠ ⊥) : B = Plane.radical.map j := by
  have hBr : B ≤ j.range := hB.trans (map_le_range _ _)
  have hmap : (B.comap j).map j = B := map_comap_eq_self hBr
  have hpre : B.comap j ≤ Plane.radical := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hB hx
    exact hj he ▸ hy
  have hm' : ⁅B.comap j,⊤⁆ = B.comap j := by
    apply map_injective hj
    rw [map_commutator, hmap, ← MonoidHom.range_eq_map, hm]
  have hne' : B.comap j ≠ ⊥ := by
    intro hz
    apply hne
    rw [← hmap, hz, Subgroup.map_bot]
  rw [← hmap, plane_moved_eq hcard hn _ hpre hm' hne']

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometry
