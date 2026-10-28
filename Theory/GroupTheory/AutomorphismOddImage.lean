module
public import Theory.GroupTheory.SylowInvariantThreeFree.Automorphism

/-!
# Odd images of two-perfect automorphism actions

Two-perfection kills the outer two-group. For a centerless target the
remaining inner image is isomorphic to a subgroup of the original target,
so its three-free subgroup theorem gives odd image order. The full action
kernel is retained; no surjectivity onto the automorphism group is assumed.

Source application: the exchanged PSL₂ factors in Aschbacher--Smith 8.3.8,
printed p.725.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {A Q : Type*} [Group A] [Group Q]

/-- Two-perfection removes the outer two-group; oddness is then tested in
the actual centerless inner model. No surjectivity of the action is needed. -/
theorem odd_card_automorphism_image_of_twoPerfect
    (f : A →* MulAut Q) (hz : center Q = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer Q))
    (hp : IsPPerfect 2 A) (hthree : ¬ 3 ∣ Nat.card A)
    (hmodel : ∀ U : Subgroup Q, IsPPerfect 2 U →
      ¬ 3 ∣ Nat.card U → Odd (Nat.card U)) : Odd (Nat.card f.range) := by
  let o := (QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp f
  have he := hp.hom_eq_one_of_isPGroup ho o
  have hf (a : A) : f a ∈ MulAut.innerSubgroup Q :=
    (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup Q) (f a)).mp
      (DFunLike.congr_fun he a)
  let b : Q ≃* MulAut.innerSubgroup Q :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  let g : A →* Q := b.symm.toMonoidHom.comp (f.codRestrict _ hf)
  have hg := hmodel g.range
    (hp.of_surjective g.rangeRestrict g.rangeRestrict_surjective)
    (fun hd => hthree (hd.trans
      (card_dvd_of_surjective g.rangeRestrict g.rangeRestrict_surjective)))
  have hcomp : MulAut.conj.comp g = f := by
    apply MonoidHom.ext
    intro a
    exact congrArg Subtype.val (b.apply_symm_apply (f.codRestrict _ hf a))
  rw [←hcomp,MonoidHom.range_comp,
    card_map_of_injective (MulAut.conj_injective_of_center_eq_bot hz)]
  exact hg

end Theory.GroupTheory
