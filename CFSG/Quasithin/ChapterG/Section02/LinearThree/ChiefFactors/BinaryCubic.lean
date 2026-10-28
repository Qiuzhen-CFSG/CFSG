module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.Order
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.BinaryFlag

/-!
# The binary homogeneous cubic and the central intersection

The earlier 12.8.5(1) homogeneous decomposition identifies U/V₁ with copies
of the natural module for the actual derived L₂(2) actor. Restricting to a
preimage of a nonidentity cubic gives coordinates in which its action is
(a,b) ↦ (b,a+b). Its norm 1+x+x² vanishes. Consequently a central section
of U/V₁ is zero. Applied to G.2.5(5), this proves S₂=V.

The homogeneous coordinate witness is an explicit earlier-source input;
its construction remains with the Section 12.8 owner. The element is in the
embedded two-residual L₁, and need not have order three before quotienting.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
12.8.5(1) and 12.8.8(5), printed pp.850–852, PDF pp.867–869.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g h : G}
  (d : Hypothesis D (ZMod 2) 1 g h)

omit [Finite G] in
/-- The actual local residual is contained in the original point stabilizer. -/
theorem local_le_pointNormalizer : D.L₁ ≤ D.L ⊓ D.G₁ :=
  map_subtype_le _

/-- Conjugation on U by an element of the actual local residual. -/
def localConj (x : D.L₁) : MulAut D.U :=
  D.U.normalizerMonoidHom
    ⟨x, le_normalizer_conjugateSpanBy D.V D.H
      (d.setup.local_le (mem_sup_left x.property))⟩

/-- The part of the genuine homogeneous coordinates of 12.8.5(1) used in
the binary series collapse. The kernel is the original V₁. -/
structure CubicSpanCoordinates (x : D.L₁) (t : ℕ) where
  coordinates : D.U →* Multiplicative (Fin t → Fin 2 → ZMod 2)
  onto : Function.Surjective coordinates
  kernel : coordinates.ker = D.V₁.subgroupOf D.U
  equivariant_zero (u : D.U) (i : Fin t) :
    (coordinates (localConj d x u)).toAdd i 0 = (coordinates u).toAdd i 1
  equivariant_one (u : D.U) (i : Fin t) :
    (coordinates (localConj d x u)).toAdd i 1 =
      (coordinates u).toAdd i 0 + (coordinates u).toAdd i 1

namespace CubicSpanCoordinates
variable {d} {x : D.L₁} {t : ℕ} (c : CubicSpanCoordinates d x t)

include c

/-- The cubic norm lies in the literal point subgroup. -/
theorem norm_mem_point (u : D.U) :
    ((u * localConj d x u * localConj d x (localConj d x u) : D.U) : G) ∈ D.V₁ := by
  have hc : c.coordinates (u * localConj d x u * localConj d x (localConj d x u)) = 1 := by
    rw [map_mul, map_mul]
    apply Multiplicative.toAdd.injective
    funext i j
    fin_cases j
    · change (c.coordinates u).toAdd i 0 +
        (c.coordinates (localConj d x u)).toAdd i 0 +
        (c.coordinates (localConj d x (localConj d x u))).toAdd i 0 = 0
      rw [c.equivariant_zero, c.equivariant_zero, c.equivariant_one]
      ring_nf
      simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]
    · change (c.coordinates u).toAdd i 1 +
        (c.coordinates (localConj d x u)).toAdd i 1 +
        (c.coordinates (localConj d x (localConj d x u))).toAdd i 1 = 0
      rw [c.equivariant_one, c.equivariant_one, c.equivariant_zero, c.equivariant_one]
      ring_nf
      simp only [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl,
        mul_zero, add_zero]
  change (u * localConj d x u * localConj d x (localConj d x u) : D.U) ∈
    D.V₁.subgroupOf D.U
  rw [← c.kernel]
  exact hc

end CubicSpanCoordinates

/-- The central triple-intersection layer vanishes modulo V, using the actual
homogeneous cubic on U/V₁. This is the first collapse in 12.8.8(5). -/
theorem binary_intersection_eq_V (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (x : D.L₁) {t : ℕ} (c : CubicSpanCoordinates d x t) :
    S₂ D g h = D.V := by
  obtain ⟨hVE, _, hEN, hcomm, helem⟩ := d.intersection hUT hf
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  have hUV : D.U ≤ normalizer (D.V : Set G) := hUT.trans d.setup.T_normalizes_V
  let : (D.V.subgroupOf D.U).Normal := (normal_subgroupOf_iff_le_normalizer hVU).mpr hUV
  let q := QuotientGroup.mk' (D.V.subgroupOf D.U)
  have hxI : (x : G) ∈ I D g h := hLI ((local_le_pointNormalizer (D := D)) x.property).1
  have hEI : S₂ D g h ≤ I D g h :=
    inf_le_left.trans (inf_le_left.trans (le_sup_left.trans le_sup_left))
  have hxE : (x : G) ∈ normalizer (S₂ D g h : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hEI).mp hEN hxI
  have hfix (u : D.U) (hu : (u : G) ∈ S₂ D g h) : q (localConj d x u) = q u := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (x : G) * (u : G) * (x : G)⁻¹ / (u : G) ∈ D.V
    rw [commutator_comm] at hcomm
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      hcomm (commutator_mem_commutator hxI hu)
  apply le_antisymm _ hVE
  intro u hu
  let uU : D.U := ⟨u, hu.1.1⟩
  have hau : ((localConj d x uU : D.U) : G) ∈ S₂ D g h :=
    (mem_normalizer_iff.mp hxE u).mp hu
  have hn : q (uU * localConj d x uU * localConj d x (localConj d x uU)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (d.setup.point_le (c.norm_mem_point uU))
  rw [map_mul, map_mul, hfix _ hau, hfix _ hu] at hn
  have hu2 : uU ^ 2 = 1 := by
    apply Subtype.ext
    let := helem
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu
  have hq2 : q uU * q uU = 1 := by
    rw [← map_mul, ← pow_two, hu2, map_one]
  rw [hq2, one_mul] at hn
  exact (QuotientGroup.eq_one_iff uU).mp hn

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
