module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.ExtensionAction
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SplitExtension
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorInner

/-!
# The simultaneous outer involution in the marked extension

The sign of either actual quaternion-axis action has kernel exactly H₁H₂:
the two-residual lies in the kernel, and the full outer image supplies a
negative sign, forcing index two. Every element outside H₁H₂ therefore
acts outerly on both original quaternion factors. For an involution,
both quotient-plane permutations are transpositions.

Combining this with the involution complement constructed from fusion
proves the normal-factor split-extension conclusion of Fong–Wong §2F(i)
for the q = 3 configuration. The action is the literal conjugation action
on Q₁Q₂. AmbientFusion continues with involution conjugacy, and
Chapter14Extension supplies the actual source consumer. This is not yet
the ambient recognition equivalence.

Source: Fong–Wong, Nagoya Math. J.36 (1969), §2F, pp.153–154;
Aschbacher–Smith I.4(G1)–(G2), printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

/-- The actual permutations of the three axes of either quaternion factor. -/
noncomputable def axisAction (i : BinaryFourPlus.C2) : c.H →* Equiv.Perm (Fin 3) where
  toFun h := (coreOuterAction c h).left i
  map_one' := by rw [map_one]; rfl
  map_mul' h k := by simp [map_mul,RegularWreathProduct.mul_left,coreOuterAction_preserves_factors]

noncomputable def axisSign (i : BinaryFourPlus.C2) : c.H →* Units ℤ :=
  Equiv.Perm.sign.comp (axisAction c i)

theorem axisSign_surjective (i : BinaryFourPlus.C2) : Function.Surjective (axisSign c i) := by
  let w : BinaryFourPlus.Wreath := ⟨fun _ => Equiv.swap 0 1,1⟩
  have hw : w ∈ diagonalSign := by
    change w.right=1 ∧ BinaryFourPlus.factorSign w=1
    decide +kernel
  rw [← coreOuterAction_range c] at hw
  obtain ⟨h,hh⟩ := hw
  have hs : axisSign c i h = -1 := by
    change Equiv.Perm.sign ((coreOuterAction c h).left i) = -1
    rw [hh]
    change Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1
    decide
  intro u
  have hu : u=1 ∨ u=-1 := (by decide : ∀ a : Units ℤ, a=1 ∨ a=-1) u
  rcases hu with rfl | rfl
  · exact ⟨1,map_one _⟩
  · exact ⟨h,hs⟩

theorem axisSign_kernel (i : BinaryFourPlus.C2) : (axisSign c i).ker = c.H₁ ⊔ c.H₂ := by
  let s := axisSign c i
  have hp : IsPGroup 2 (Units ℤ) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide)
  have hR : pResidual 2 c.H ≤ s.ker :=
    sInf_le ⟨inferInstance,(hp.to_subgroup s.range).of_equiv
      (QuotientGroup.quotientKerEquivRange s).symm⟩
  rw [H_residual c] at hR
  apply (eq_of_le_of_card_ge hR ?_).symm
  have hi : s.ker.index = 2 := by
    rw [index_eq_card,Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective s (axisSign_surjective c i)).toEquiv,
      Nat.card_eq_fintype_card]
    decide
  have hc := s.ker.card_mul_index
  rw [hi,H_card c] at hc
  rw [product_card c]
  omega

/-- Every involution outside the original residual acts by a transposition
on both marked quaternion quotient planes. -/
theorem outside_involution_axisAction (n : c.H) (hn : orderOf n = 2)
    (hout : n ∉ c.H₁ ⊔ c.H₂) (i : BinaryFourPlus.C2) :
    orderOf (axisAction c i n) = 2 ∧ Equiv.Perm.sign (axisAction c i n) ≠ 1 := by
  have hs : Equiv.Perm.sign (axisAction c i n) ≠ 1 := by
    intro hh
    apply hout
    rw [← axisSign_kernel c i]
    exact hh
  refine ⟨orderOf_eq_prime ?_ (fun hh => hs (by rw [hh,map_one])),hs⟩
  have hn2 : n^2=1 := hn ▸ pow_orderOf_eq_one n
  rw [← map_pow,hn2,map_one]

theorem outside_bothOuter (n : c.H) (hout : n ∉ c.H₁ ⊔ c.H₂) :
    (quaternionCoreData c).BothOuter (MulAut.conjNormal n) := by
  have hi (i : BinaryFourPlus.C2) : (coreOuterAction c n).left i ≠ 1 := by
    intro hh
    apply hout
    rw [← axisSign_kernel c i]
    change Equiv.Perm.sign ((coreOuterAction c n).left i) = 1
    rw [hh,map_one]
  exact (quaternionCoreData c).bothOuter_of_nontrivial_axes
    (MulAut.conjNormal n) (coreOuterAction_preserves_factors c n) (hi 1) (hi _)

/-- The complement is constructed from ambient fusion, with both actual
axis actions retained; it is not an abstract order-two extension parameter. -/
theorem exists_fused_involution_complement_with_action :
    ∃ (z : G) (n : c.H), orderOf z = 2 ∧ c.H = centralizer ({z} : Set G) ∧
      orderOf n = 2 ∧ n ∉ c.H₁ ⊔ c.H₂ ∧
      (c.H₁ ⊔ c.H₂).IsComplement' (zpowers n) ∧ IsConj z (n:G) ∧
      (quaternionCoreData c).BothOuter (MulAut.conjNormal n) ∧
      (∀ i : BinaryFourPlus.C2, orderOf ((coreOuterAction c n).left i) = 2 ∧
        Equiv.Perm.sign ((coreOuterAction c n).left i) ≠ 1) := by
  obtain ⟨z,n,hz,hH,hn,hout,hcomp,hf⟩ := exists_fused_involution_complement c
  exact ⟨z,n,hz,hH,hn,hout,hcomp,hf,outside_bothOuter c n hout,
    outside_involution_axisAction c n hn hout⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
