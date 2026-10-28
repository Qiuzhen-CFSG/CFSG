module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.QuotientSetup
public import Theory.SpecificGroups.PSL3Four.IndexTwoFixedInvolutions

/-!
# The PSL₃(4) fixed-group input to the commuting-Sylow dichotomy

An actual equivalence L/O₂(L) ≃ PSL₃(4) transports the induced quotient
automorphism and restricts to an equivalence of their full fixed subgroups.
It preserves outer order-two action, nonperfectness, subgroup index, and
involutions. Thus the E₉-kernel/Q₈-quotient argument applies to the actual
`quotientFixed`, with the earlier fixed-group table retained explicitly.

For the centralizer image, index two already proves nonperfectness. The
last theorem therefore puts every quotient fixed involution in that image.
The local geometry producing an involution outside the image, and the
discharge of the structural table input, belong to the final assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed p.1190, the PSL₃(4) exclusion between (+) and (!),
using the outer-automorphism table 16.1.4 on printed p.1171.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
open ComponentTransfer.Intrinsic Matrix.PSL3Four.IndexTwoFixedInvolutions
variable {G : Type*} [Group G] {L : Subgroup G} {r : G}

/-- Transfer the exact PSL₃(4) fixed-group table through an actual quotient
equivalence. Every square-one element of the full fixed group lies in D. -/
theorem quotientFixed_sq_eq_one_mem_of_linear_table
    (hn : r ∈ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL)
    (hTable : FixedGroupTable (MulAut.congr e (quotientAction hn)))
    (ha : orderOf (quotientAction hn) = 2)
    (houter : ¬ ∃ x : L ⧸ pCore 2 L, quotientAction hn = MulAut.conj x)
    (hperfect : ¬ Group.IsPerfect (quotientFixed hn))
    (D : Subgroup (quotientFixed hn)) (hD : D.index = 2)
    (x : quotientFixed hn) (hx : x ^ 2 = 1) : x ∈ D := by
  let d := MulAut.fixedSubgroupCongr e (quotientAction hn)
  have ha' : orderOf (MulAut.congr e (quotientAction hn)) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).trans ha
  have ho' : ¬ ∃ y : Matrix.PSL3Four.PSL,
      MulAut.congr e (quotientAction hn) = MulAut.conj y :=
    fun h => houter ((MulAut.congr_inner_iff e (quotientAction hn)).mp h)
  have hp' : ¬ Group.IsPerfect (MulAut.congr e (quotientAction hn)).fixedSubgroup := by
    intro hp
    let := hp
    exact hperfect (Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective)
  have hm := fixed_sq_eq_one_mem_of_table _ hTable ha' ho' hp'
    (D.map d.toMonoidHom) ((D.index_map_equiv d).trans hD) (d x)
    (by rw [← map_pow, hx, map_one])
  exact (Subgroup.mem_map_iff_mem d.injective).mp hm

/-- Every involution of the nonperfect quotient fixed group lies in every
index-two subgroup, conditional only on the displayed earlier model table. -/
theorem quotientFixed_involution_mem_of_linear_table
    (hn : r ∈ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL)
    (hTable : FixedGroupTable (MulAut.congr e (quotientAction hn)))
    (ha : orderOf (quotientAction hn) = 2)
    (houter : ¬ ∃ x : L ⧸ pCore 2 L, quotientAction hn = MulAut.conj x)
    (hperfect : ¬ Group.IsPerfect (quotientFixed hn))
    (D : Subgroup (quotientFixed hn)) (hD : D.index = 2)
    (x : quotientFixed hn) (hx : orderOf x = 2) : x ∈ D :=
  quotientFixed_sq_eq_one_mem_of_linear_table hn e hTable ha houter hperfect D hD x
    (by simpa only [hx] using pow_orderOf_eq_one x)

/-- In the actual centralizer-image case, its index supplies nonperfectness.
An involution outside this image would contradict this model conclusion. -/
theorem quotientFixed_involution_mem_image_of_linear_table
    (hn : r ∈ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL)
    (hTable : FixedGroupTable (MulAut.congr e (quotientAction hn)))
    (ha : orderOf (quotientAction hn) = 2)
    (houter : ¬ ∃ x : L ⧸ pCore 2 L, quotientAction hn = MulAut.conj x)
    (hi : (imageInFixed hn).index = 2)
    (x : L ⧸ pCore 2 L) (hfixed : x ∈ quotientFixed hn) (hx : orderOf x = 2) :
    x ∈ centralizerImage hn := by
  exact quotientFixed_involution_mem_of_linear_table hn e hTable ha houter
    (quotientFixed_not_perfect hn hi) (imageInFixed hn) hi ⟨x, hfixed⟩
    ((Subgroup.orderOf_coe ⟨x, hfixed⟩).symm.trans hx)

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
