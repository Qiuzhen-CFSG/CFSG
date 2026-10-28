module
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Odd two-perfect images in PSL₂ involution centralizers

The reflected cyclic torus makes an involution centralizer dihedral.
The parity character kills reflections in a two-perfect image; that image
is then abelian and of odd order. If the outer automorphism group is a
two-group, the same argument applies to the actual automorphism action
centralizing an inner involution. Both original homomorphisms are retained.

Source: Huppert II.8.3--4, as used in Aschbacher--Smith, proof of 12.6.26,
printed p.833, to kill the two-core of the original residual action.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private def parity (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) := {
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' a b := by
    cases a <;> cases b <;> simp
    change (0 : ZMod 2) = 1 + 1
    exact (ZMod.natCast_self 2).symm }

private theorem dihedral_image_odd {A : Type*} [_root_.Group A] [Finite A]
    (hp : IsPPerfect 2 A) {n : ℕ} (f : A →* DihedralGroup n) :
    Odd (Nat.card f.range) := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hz := hp.hom_eq_one_of_isPGroup
    (IsPGroup.of_card (p := 2) (n := 1) (by simp)) ((parity n).comp f)
  have hr (x : A) : ∃ i, f x = DihedralGroup.r i := by
    cases he : f x with
    | r i => exact ⟨i,rfl⟩
    | sr i =>
      have hh := congrArg Multiplicative.toAdd (DFunLike.congr_fun hz x)
      change (parity n (f x)).toAdd = 0 at hh
      rw [he] at hh
      change (1 : ZMod 2) = 0 at hh
      exact (one_ne_zero hh).elim
  let : IsMulCommutative f.range := ⟨⟨by
    rintro ⟨x,a,rfl⟩ ⟨y,b,rfl⟩
    obtain ⟨i,hi⟩ := hr a
    obtain ⟨j,hj⟩ := hr b
    apply Subtype.ext
    change f a * f b = f b * f a
    simp only [hi,hj,DihedralGroup.r_mul_r,add_comm]⟩⟩
  let : CommGroup f.range := IsMulCommutative.instCommGroup
  exact Nat.coprime_two_left.mp (coprime_card_of_isPPerfect_commGroup
    (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective))

/-- A two-perfect group acting inside an odd-field involution centralizer
has odd image. The map is retained, with no surjectivity premise. -/
theorem odd_image_of_twoPerfect_centralizing_involution
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (t : PSL(2,F)) (ht : orderOf t = 2)
    {A : Type*} [_root_.Group A] [Finite A] (hp : IsPPerfect 2 A)
    (f : A →* PSL(2,F)) (hf : ∀ a, Commute (f a) t) :
    Odd (Nat.card f.range) := by
  obtain ⟨R,s,hR,_,hs,hsR,hi,hc,_⟩ := psl2_reflected_torus_card hF
    (show GorensteinWalter.IsInvolution t from ⟨by intro h; simp [h] at ht,
      by simpa only [ht] using pow_orderOf_eq_one t⟩)
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted R s hR hs.2 hsR hi
  let C := centralizer ({t} : Set PSL(2,F))
  let j : A →* C := f.codRestrict C (fun a => mem_centralizer_singleton_iff.mpr (hf a).eq)
  let d : C ≃* DihedralGroup (Nat.card R) := (MulEquiv.subgroupCongr hc).trans e
  have hh := dihedral_image_odd hp (d.toMonoidHom.comp j)
  rw [MonoidHom.range_comp,card_map_of_injective d.injective] at hh
  have hj : C.subtype.comp j = f := rfl
  rw [←hj,MonoidHom.range_comp,card_map_of_injective C.subtype_injective]
  exact hh

/-- The full marked automorphism action has odd image when its two-perfect
actor centralizes an inner involution and the outer group is a two-group. -/
theorem odd_automorphism_image_of_twoPerfect_centralizing_inner_involution
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (ho : IsPGroup 2 (MulAut.Outer PSL(2,F)))
    (t : PSL(2,F)) (ht : orderOf t = 2)
    {A : Type*} [_root_.Group A] [Finite A] (hp : IsPPerfect 2 A)
    (f : A →* MulAut PSL(2,F)) (hf : ∀ a, Commute (f a) (MulAut.conj t)) :
    Odd (Nat.card f.range) := by
  have hz := psl2_center_eq_bot F
  let o := (QuotientGroup.mk' (MulAut.innerSubgroup PSL(2,F))).comp f
  have he := hp.hom_eq_one_of_isPGroup ho o
  have hfi (a : A) : f a ∈ MulAut.innerSubgroup PSL(2,F) :=
    (QuotientGroup.eq_one_iff (f a)).mp (DFunLike.congr_fun he a)
  let b : PSL(2,F) ≃* MulAut.innerSubgroup PSL(2,F) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  let g : A →* PSL(2,F) := b.symm.toMonoidHom.comp (f.codRestrict _ hfi)
  have hg (a : A) : MulAut.conj (g a) = f a :=
    congrArg Subtype.val (b.apply_symm_apply (f.codRestrict _ hfi a))
  have hgt (a : A) : Commute (g a) t := by
    apply (MulAut.conj_injective_of_center_eq_bot hz)
    simp only [map_mul,hg]
    exact (hf a).eq
  have hh := odd_image_of_twoPerfect_centralizing_involution hF t ht hp g hgt
  have hcomp : MulAut.conj.comp g = f := MonoidHom.ext hg
  rw [←hcomp,MonoidHom.range_comp,
    card_map_of_injective (MulAut.conj_injective_of_center_eq_bot hz)]
  exact hh

end Theory.PSL2
