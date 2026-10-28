module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Selection
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift

/-!
# An actual cubic actor in the original plane residual

The original returning permutation has order three in the natural A₆
quotient. Lift it to an odd-order element of L. Since the quotient kernel
is a two-group, the lift has order three. Equivariance preserves its plane
and moves the marked point, and its odd order puts it in O²(N_L(V₂)).

Source: Aschbacher–Smith, Proposition 13.5.16, printed pp.921–922.
-/

universe u

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open PlaneGeometry.TwoBlocks
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (b : Conclusions D M 6 g)
include d h b

/-- The returning actor can be chosen with actual order three. -/
theorem exists_returning_cubic :
    ∃ r : G, r ∈ Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂ ∧
      r ∈ normalizer (V₂ : Set G) ∧ r ∉ D.H ∧ orderOf r = 3 := by
  obtain ⟨a,ha,hplane,y,hy,hyr,hyP,hyG⟩ := ReturningPlane.exists_original_returning d h
  let f := (localMap d).rangeRestrict
  let q := f y
  have hq3 : orderOf q = 3 := by
    rw [←Subgroup.orderOf_coe]
    change orderOf (localMap d y) = 3
    rw [hyr]
    change orderOf (MulAut.conj a.val pairRotation⁻¹) = 3
    rw [(MulAut.conj a.val).orderOf_eq,orderOf_inv]
    exact orderOf_eq_prime (by decide +kernel : pairRotation ^ 3 = 1)
      (by decide +kernel : pairRotation ≠ 1)
  obtain ⟨r,hrOdd,hrq⟩ := f.exists_pRegular_lift (localMap d).rangeRestrict_surjective
    2 Nat.prime_two q (by rw [hq3]; decide)
  have hrimage : localMap d r = localMap d y :=
    congrArg (fun t : (localMap d).range => (t : Equiv.Perm (Fin 6))) hrq
  have hr3 : orderOf r = 3 := by
    have he := (localMap d).orderOf_map_eq_of_coprime_of_isPGroup_ker
      (localMap_kernel_two d (b.four.2 rfl)) r (Nat.prime_two.coprime_iff_not_dvd.mpr hrOdd)
    rw [←he,hrimage]
    exact (Subgroup.orderOf_coe q).trans hq3
  have hrP : r.val ∈ normalizer (V₂ : Set G) := by
    apply (ReturningPlane.localNormalizer_mem d V₂ (d.plane_le_seed.trans d.seed_le) r).mpr
    rw [hrimage]
    exact (ReturningPlane.localNormalizer_mem d V₂ (d.plane_le_seed.trans d.seed_le) y).mp hyP
  have hrH : r.val ∉ D.H := by
    intro hrH
    have hrG : r.val ∈ D.Gz := b.six.1 ▸ hrH
    have hrPt := (ReturningPlane.localNormalizer_mem d D.V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) r).mp
      (h.normalizer_point_eq.symm ▸ hrG)
    rw [hrimage] at hrPt
    exact hyG (h.normalizer_point_eq ▸ (ReturningPlane.localNormalizer_mem d D.V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) y).mpr hrPt)
  let K := D.L ⊓ normalizer (V₂ : Set G)
  have hrK : r.val ∈ K := ⟨r.property,hrP⟩
  have hrRes : (⟨r.val,hrK⟩ : K) ∈ pResidual 2 K := by
    apply mem_pResidual_of_orderOf_coprime
    have ho : orderOf (⟨r.val,hrK⟩ : K) = 3 := by
      rw [←Subgroup.orderOf_coe,Subgroup.orderOf_coe r,hr3]
    rw [ho]
    decide
  exact ⟨r.val,mem_map_of_mem K.subtype hrRes,hrP,hrH,(Subgroup.orderOf_coe r).trans hr3⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
