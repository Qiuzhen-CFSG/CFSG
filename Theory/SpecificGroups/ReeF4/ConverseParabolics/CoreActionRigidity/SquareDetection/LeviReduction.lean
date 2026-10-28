module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure

/-!
# The radical–torus factorization when the SL₂ coordinate vanishes

A full-Levi factor whose projection has trivial SL₂ coordinate centralizes
that Levi: every commutator lies in both the exact radical kernel and the
full Levi, whose intersection is trivial. The faithful subsystem–torus
product and the trivial center of SL₂ in characteristic two then place
this factor in the actual complementary torus.

This uses the public kernel and disjointness theorems, so no unfolding of
the full-parabolic projection or choice of its quotient representative is
needed. Source: GLS3, Theorem 2.6.5(f,g), and the linear Ree local factor
in Aschbacher–Smith F.1.12(I)(5), printed p.263 (`refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection
open LargeLocalSeeds FullLeviRepresentation
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open SectionGeometry.LinearRadical (fullLevi)
variable {m : ℕ}

private theorem central_fullLevi_mem_complement (hm : 1 ≤ m)
    (l : Model m) (hl : l ∈ fullLevi m)
    (hc : ∀ y ∈ fullLevi m, l * y = y * l) :
    ∃ c : (CoefficientField m)ˣ, l = torusElement 1 c := by
  have hmem : l ∈ (productHom hm).range := by rw [productHom_range]; exact hl
  obtain ⟨⟨s, c⟩, he⟩ := hmem
  change seedLeviHom m s * complementHom m c = l at he
  have hs (y : fixedLevi (canonicalLocalBlockInput m) .linear) : s * y = y * s := by
    apply seedLeviHom_injective m
    simp only [map_mul]
    have h := hc (seedLeviHom m y) (seedLeviHom_le_fullLevi m ⟨y, rfl⟩)
    rw [← he] at h
    have h' : (seedLeviHom m s * seedLeviHom m y) * complementHom m c =
        (seedLeviHom m y * seedLeviHom m s) * complementHom m c := by
      calc
        _ = (seedLeviHom m s * complementHom m c) * seedLeviHom m y := by
          rw [mul_assoc, (seed_commutes_complement hm y c).eq, ← mul_assoc]
        _ = _ := h.trans (mul_assoc _ _ _).symm
    exact mul_right_cancel h'
  let e := LinearProjection.fixedLeviEquivSL hm (canonicalLocalBlockInput m)
  have hscent : e s ∈ center (LinearSL m) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    exact (e.map_mul y s).symm.trans
      ((congrArg e (hs y).symm).trans (e.map_mul s y))
  have hsone : s = 1 := by
    apply e.injective
    rw [map_one]
    simpa only [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot, mem_bot] using hscent
  refine ⟨c, ?_⟩
  rw [hsone, map_one, one_mul, complementHom_apply] at he
  exact he.symm

/-- Trivial SL₂ image leaves precisely a radical factor and the actual
complementary torus. This uses the exact kernel and full-Levi disjointness,
without unfolding the full-parabolic projection. -/
theorem exists_radical_torus_factors (hm : 1 ≤ m) (b : parabolic m .linear)
    (hb : (linearProjection hm b).1 = 1) :
    ∃ r ∈ radical m .linear, ∃ c : (CoefficientField m)ˣ,
      b.val = r * torusElement 1 c := by
  obtain ⟨r, hr, l, hl, he⟩ := SectionGeometry.LinearRadical.exists_radical_fullLevi_factors
    m b.val (by
      simpa only [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic]
        using b.property)
  have hr' : r ∈ radical m .linear := by rwa [radical_eq_rootRadical]
  let rP : parabolic m .linear := ⟨r, radical_le_parabolic m .linear hr'⟩
  let lP : parabolic m .linear := ⟨l, linear_fullLevi_le_parabolic m hl⟩
  have hrker : linearProjection hm rP = 1 := by
    apply (linearProjection hm).mem_ker.mp
    rw [linearProjection_ker]
    exact hr'
  have hlproj : linearProjection hm lP = linearProjection hm b := by
    have hfactor : rP * lP = b := Subtype.ext he
    rw [← hfactor, map_mul, hrker, one_mul]
  have hlcent : ∀ y ∈ fullLevi m, l * y = y * l := by
    intro y hy
    let yP : parabolic m .linear := ⟨y, linear_fullLevi_le_parabolic m hy⟩
    have himg : Commute (linearProjection hm lP) (linearProjection hm yP) := by
      change linearProjection hm lP * linearProjection hm yP =
        linearProjection hm yP * linearProjection hm lP
      apply Prod.ext
      · simp only [Prod.fst_mul, hlproj, hb, one_mul, mul_one]
      · exact mul_comm _ _
    have hk : ⁅lP, yP⁆ ∈ intrinsicRadical m .linear := by
      rw [← linearProjection_ker hm, MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr himg.eq
    have hk' : ⁅l, y⁆ ∈ radical m .linear := hk
    have hl' : ⁅l, y⁆ ∈ fullLevi m :=
      (commutator_le_self _) (commutator_mem_commutator hl hy)
    have hz := Subgroup.disjoint_def.mp (linear_radical_disjoint_fullLevi m) hk' hl'
    exact commutatorElement_eq_one_iff_mul_comm.mp hz
  obtain ⟨c, hc⟩ := central_fullLevi_mem_complement hm l hl hlcent
  exact ⟨r, hr', c, he.symm.trans (congrArg (r * ·) hc)⟩

end ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection
