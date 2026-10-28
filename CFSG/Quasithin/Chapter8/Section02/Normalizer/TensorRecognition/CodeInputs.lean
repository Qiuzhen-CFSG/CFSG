module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CodeObstruction
public import Theory.GroupTheory.DihedralFiveTwist
public import Theory.Representation.CyclicFixedRank

/-!
# Constructing the linear contradiction from the marked code extension

In the source's hypothetical T-normalized extension, let D be the marked
image I/P ≃ D₁₀ and let z be the central cubic of the triple-A₆ factor.
An outer involution t inverts z and fixes the marked reflection v of D.
The dihedral calculation chooses s=t or tv centralizing all of D. It still
inverts z, so its fixed rank is six on the twelve-dimensional literal P/U.
Generation by the rotation commutators makes the order-five action
fixed-point free. The existing code obstruction now applies.

The rank calculation uses only inversion of the cubic and rank-nullity;
the order-five divisibility theorem replaces the source's decomposition
into rank-four irreducibles. Both operate on the original quotient carrier.

The construction of the marked D₁₀ image belongs to the small-action sieve.
The local cubic, its fixed-point-free action, and the outer involution
lift with the displayed conjugation relations remain explicit source
inputs. In particular this module does not yet assert nonnormalization
of O²(I) from the full Chapter 8 setup.

Source: Aschbacher–Smith, Proposition 8.2.8(6), printed p.719 (PDF p.736
of refs/quasithin.pdf); the cubic comes from H.16.1's sextet action.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G H : Type*} [Group G] [Group H] [Finite G]
  (I U : Subgroup G) [(U.subgroupOf (I.pCoreIn 2)).Normal]
  [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]

/-- The marked outer involution gives the actual rank-six actor on P/U.
Neither its rank nor centralization of D is an input. -/
theorem code_involution_fixed_rank
    (ρ : Representation (ZMod 2) H (CoreSection I U))
    (D : Subgroup H) (e : D ≃* DihedralGroup 5) (z t : H)
    (hz : orderOf z = 3) (ht : t ^ 2 = 1)
    (hn : t ∈ normalizer (D : Set H))
    (htv : Commute t (e.symm (.sr 0) : H))
    (hvz : Commute (e.symm (.sr 0) : H) z)
    (htz : t * z = z ^ 2 * t)
    (hzfree : ∀ p, ρ z p = p → p = 0)
    (hdim : Module.finrank (ZMod 2) (CoreSection I U) = 12) :
    ∃ s : H, (s = t ∨ s = t * (e.symm (.sr 0) : H)) ∧
      orderOf s = 2 ∧ (∀ d : D, Commute s (d : H)) ∧
      Module.finrank (ZMod 2) (LinearMap.ker (ρ s - LinearMap.id)) = 6 := by
  obtain ⟨s, hchoice, hs, hc⟩ :=
    exists_involution_twist_centralizing_dihedral_five D e t hn ht htv
  have hsz : s * z = z ^ 2 * s := by
    rcases hchoice with rfl | rfl
    · exact htz
    · calc
        (t * (e.symm (.sr 0) : H)) * z =
            (t * z) * (e.symm (.sr 0) : H) := by rw [mul_assoc, hvz.eq, ← mul_assoc]
        _ = z ^ 2 * (t * (e.symm (.sr 0) : H)) := by rw [htz, mul_assoc]
  have hsne : s ≠ 1 := by
    intro he
    have hzz : z = z * z := by simpa only [he, one_mul, mul_one, pow_two] using hsz
    have hz1 : z = 1 := mul_left_cancel (hzz.symm.trans (mul_one z).symm)
    rw [hz1, orderOf_one] at hz
    omega
  refine ⟨s, hchoice, orderOf_eq_prime hs hsne, hc, ?_⟩
  have hd := CyclicFixedRank.twice_fixedRank_of_inverted_cubic ρ z s
    (hz ▸ pow_orderOf_eq_one z) hs hsz hzfree
  rw [hdim] at hd
  omega

/-- The source code contradiction from the marked local extension and
cyclic commutator generation, with all final obstruction inputs constructed. -/
theorem code_obstruction_of_cubic_extension
    (ρ : Representation (ZMod 2) H (CoreSection I U))
    (D : Subgroup H) (e : D ≃* DihedralGroup 5) (z t : H)
    (hz : orderOf z = 3) (ht : t ^ 2 = 1)
    (hn : t ∈ normalizer (D : Set H))
    (htv : Commute t (e.symm (.sr 0) : H))
    (hvz : Commute (e.symm (.sr 0) : H) z)
    (htz : t * z = z ^ 2 * t)
    (hzfree : ∀ p, ρ z p = p → p = 0)
    (hdim : Module.finrank (ZMod 2) (CoreSection I U) = 12)
    (hgen : subspaceCommutator ρ ⊤ (zpowers (e.symm (.r 1) : H)) = ⊤) : False := by
  obtain ⟨s, _, _, hc, hd⟩ :=
    code_involution_fixed_rank I U ρ D e z t hz ht hn htv hvz htz hzfree hdim
  have hx : orderOf (e.symm (.r 1) : H) = 5 := by
    rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, DihedralGroup.orderOf_r_one]
  exact code_fixed_rank_obstruction I U ρ (e.symm (.r 1)) s hx (hc _)
    (CyclicFixedRank.fixedFree_of_commutator_eq_top ρ _ hgen) hd

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
