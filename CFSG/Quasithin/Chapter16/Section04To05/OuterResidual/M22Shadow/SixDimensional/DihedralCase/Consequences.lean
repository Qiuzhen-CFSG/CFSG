module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.Basic
public import Theory.SpecificGroups.SymmetricFiveSylow
public import Theory.Representation.AutomorphismFixedLine

/-!
# Sylow and fixed-line consequences of the actual local actions

The local S₅ comparison identifies the published Sylow action image with D₈.
For the equality outcome of the later component sieve, normality of the local
residual image makes its two-element fixed subgroup invariant. The unique
nonidentity fixed element z is therefore fixed by M⁺. Its full S₅ stabilizer
and the second local S₅ have equal orders, so the latter is all of M⁺ and
fixes r, contrary to the given nontrivial action of the actual local residual.

Normality of the residual image remains an explicit premise: the component
and dimension-six sieve must establish it. No component theorem, symmetry
automorphism, homomorphic lift, or seven-point recognition is asserted here.

Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
variable {G : Type*} [Group G]

def zVector (L : Subgroup G) (r z : G) : shadowSpace L r z :=
  ⟨z, (show zpowers z ≤ shadowSpace L r z from le_sup_right.trans le_sup_right)
    (mem_zpowers z)⟩
def rVector (L : Subgroup G) (r z : G) : shadowSpace L r z :=
  ⟨r, (show zpowers r ≤ shadowSpace L r z from le_sup_left.trans le_sup_right)
    (mem_zpowers r)⟩

theorem image_fixed_iff (L : Subgroup G) (g r z : G) (A : Subgroup G)
    (hA : A ≤ shadowOvergroup L g r z) (v : shadowSpace L r z) :
    v ∈ MulAction.fixedPoints (imageSubgroup L g r z A) (shadowSpace L r z) ↔
      (v : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hv
    apply mem_centralizer_iff.mpr
    intro a ha
    let m : shadowOvergroup L g r z := ⟨a, hA ha⟩
    let b : imageSubgroup L g r z A :=
      ⟨(shadowAction L g r z).rangeRestrict m, ⟨m, ha, rfl⟩⟩
    have he := congrArg (fun w : shadowSpace L r z => (w : G)) (hv b)
    change a * (v : G) * a⁻¹ = v at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hv b
    obtain ⟨m, hm, he⟩ := b.property
    change b.val.val v = v
    rw [← he]
    apply Subtype.ext
    change (m : G) * v * (m : G)⁻¹ = v
    rw [mem_centralizer_iff.mp hv m hm, mul_inv_cancel_right]

theorem image_le_stabilizer (L : Subgroup G) (g r z : G) (A : Subgroup G)
    (v : shadowSpace L r z) (hA : A ≤ centralizer ({(v : G)} : Set G)) :
    imageSubgroup L g r z A ≤ MulAction.stabilizer (Image L g r z) v := by
  rintro a ⟨m, hm, rfl⟩
  change shadowAction L g r z m v = v
  apply Subtype.ext
  change (m : G) * v * (m : G)⁻¹ = v
  have hc : (m : G) * v = v * (m : G) := mem_centralizer_singleton_iff.mp (hA hm)
  rw [hc, mul_inv_cancel_right]

variable [Finite G]

theorem sylow_dihedral (L : Subgroup G) (g r z : G) (T : Sylow 2 G)
    [IsMulCommutative (shadowSpace L r z)]
    (hTL : componentSylow T L ≤ normalizer (shadowSpace L r z : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hgen : (T : Subgroup G) = componentSylow T L ⊔ (zpowers z ⊔ zpowers r))
    (e : imageSubgroup L g r z (localNormalizer L r z) ≃* Equiv.Perm (Fin 5)) :
    ∃ S : Sylow 2 (Image L g r z),
      (S : Subgroup (Image L g r z)) = imageSubgroup L g r z T ∧
      imageSubgroup L g r z T = imageSubgroup L g r z (componentSylow T L) ∧
      Nonempty (S ≃* DihedralGroup 4) := by
  have hT := sylow_le_shadowOvergroup L g r z T hTL hTN hgen
  obtain ⟨S, hS⟩ := sylow_image L g r z T hT
  have hE := sylow_image_eq L g r z T hT hgen
  have hSK : (S : Subgroup (Image L g r z)) ≤
      imageSubgroup L g r z (localNormalizer L r z) := by
    rw [hS, hE]
    exact imageSubgroup_mono L g r z (le_inf inf_le_right hTL)
  let P := S.subtype hSK
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨d⟩ := Equiv.Perm.sylow_two_equiv_dihedral_five Q
  refine ⟨S, hS, hE, ⟨?_⟩⟩
  exact (subgroupOfEquivOfLe hSK).symm.trans
    (((P : Subgroup (imageSubgroup L g r z (localNormalizer L r z))).equivMapOfInjective
      e.toMonoidHom e.injective).trans d)

theorem fixed_line_obstruction (L : Subgroup G) (g r z : G)
    (hz : orderOf z = 2)
    (hnormal : (imageSubgroup L g r z (localResidual L r z)).Normal)
    (hfixed : shadowSpace L r z ⊓ centralizer (localResidual L r z : Set G) = zpowers z)
    (hstab : imageSubgroup L g r z (localNormalizer L r z) =
      MulAction.stabilizer (Image L g r z) (zVector L r z))
    (J : Subgroup G) (hJ : J ≤ centralizer ({r} : Set G))
    (eL : imageSubgroup L g r z (localNormalizer L r z) ≃* Equiv.Perm (Fin 5))
    (eJ : imageSubgroup L g r z J ≃* Equiv.Perm (Fin 5))
    (hmove : ¬ localResidual L r z ≤ centralizer ({r} : Set G)) : False := by
  classical
  let := hnormal
  have hB : localResidual L r z ≤ shadowOvergroup L g r z :=
    (map_subtype_le _).trans (localNormalizer_le L g r z)
  have hz' : zVector L r z ≠ 1 := by
    intro he
    have he' : z = 1 := congrArg (fun v : shadowSpace L r z => (v : G)) he
    simp [he'] at hz
  have hline (v : shadowSpace L r z) :
      v ∈ MulAction.fixedPoints (imageSubgroup L g r z (localResidual L r z))
          (shadowSpace L r z) ↔ v = 1 ∨ v = zVector L r z := by
    rw [image_fixed_iff L g r z _ hB]
    have hmem : (v : G) ∈ centralizer (localResidual L r z : Set G) ↔
        (v : G) ∈ zpowers z := by
      rw [← hfixed]
      exact ⟨fun hh => ⟨v.property, hh⟩, And.right⟩
    rw [hmem, mem_zpowers_iff_mem_range_orderOf, hz]
    constructor
    · intro hv
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hv
      have hi' : i < 2 := Finset.mem_range.mp hi
      interval_cases i
      · left; exact Subtype.ext (by simpa using he.symm)
      · right
        apply Subtype.ext
        change (v : G) = z
        simpa using he.symm
    · rintro (rfl | rfl)
      · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
      · exact Finset.mem_image.mpr ⟨1, by simp, by simp [zVector]⟩
  apply MulDistribMulAction.fixedPoint_stabilizer_obstruction
    (zVector L r z) (rVector L r z) hz'
    (imageSubgroup L g r z (localResidual L r z)) hline
    (imageSubgroup L g r z (localNormalizer L r z)) (imageSubgroup L g r z J)
    hstab (image_le_stabilizer L g r z J (rVector L r z) hJ)
    (by rw [Nat.card_congr eL.toEquiv, Nat.card_congr eJ.toEquiv])
  by_contra hn
  push Not at hn
  apply hmove
  intro a ha
  apply mem_centralizer_singleton_iff.mpr
  let m : shadowOvergroup L g r z := ⟨a, hB ha⟩
  let b : imageSubgroup L g r z (localResidual L r z) :=
    ⟨(shadowAction L g r z).rangeRestrict m, ⟨m, ha, rfl⟩⟩
  have he := congrArg (fun v : shadowSpace L r z => (v : G)) (hn b)
  change a * r * a⁻¹ = r at he
  exact mul_inv_eq_iff_eq_mul.mp he

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
