module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.Commutator.TwoCoverComparison
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# Involutory lifts exclude nontrivial perfect central two-covers of SL₃(2)

The actual exceptional isomorphism PSL₂(7) ≃ SL₃(2) transfers a perfect
central two-cover to the setting of the two-cover comparison theorem.
A nontrivial kernel would identify its derived group, hence the whole
perfect cover, with SL₂(7). Every square-one matrix there is scalar, so
every involution of the cover has trivial image in the centerless SL₃(2).
Thus a square-one lift with nonidentity image forces the kernel to vanish.

The comparison uses the checked ATLAS exceptional isomorphism, with its
attribution retained in Theory/AtlasPort/ExceptionalIsomorphisms/Order168.lean.
This is the intrinsic cover argument used in Aschbacher–Smith 14.7.72,
printed p.1076 (PDF p.1093), combined manuscript of 1 March 2004.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace BinaryLinearThree.CentralCover
private instance sevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem involution_central (x : SL(2,ZMod 7)) (hx : x ^ 2 = 1) :
    x ∈ center SL(2,ZMod 7) := by
  have hd : (SpecialLinearGroup.toGL x).det = 1 := by
    apply Units.ext
    exact x.property
  have hx' : (SpecialLinearGroup.toGL x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
      (by decide : (2 : ZMod 7) ≠ 0) (SpecialLinearGroup.toGL x) hx' hd with h | h
  · have he : x = 1 := SpecialLinearGroup.toGL_injective (by simpa using h)
    rw [he]
    exact (center _).one_mem
  · have he : x = -1 := Subtype.ext (congrArg Units.val h)
    rw [he, mem_center_iff]
    intro y
    apply Subtype.ext
    change y.val * (-1 : SL(2,ZMod 7)).val = (-1 : SL(2,ZMod 7)).val * y.val
    simp

/-- A square-one lift of a nonidentity element rules out every nontrivial
perfect central two-cover of the actual binary SL₃. -/
theorem kernel_eq_bot_of_involution
    {E : Type*} [_root_.Group E] [Finite E] [_root_.Group.IsPerfect E]
    (f : E →* SL(3,ZMod 2)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (x : E) (hx : x ^ 2 = 1) (hfx : f x ≠ 1) : f.ker = ⊥ := by
  by_contra hn
  let e := Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two
  let f' := e.symm.toMonoidHom.comp f
  have hker : f'.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ e.symm.injective
  let g := GorensteinWalter.sl2ProjectiveProjection (ZMod 7)
  obtain ⟨hg, hgc, hgcard, hg2, hperfect, hdihedral⟩ :=
    GorensteinWalter.sl2_projective_cover_model (ZMod 7)
      (by norm_num) (by norm_num)
  let : _root_.Group.IsPerfect SL(2,ZMod 7) := hperfect
  obtain ⟨r⟩ := CentralExtension.commutator_mulEquiv_of_central_two_covers f' g
    (e.symm.surjective.comp hf) hg (by rw [hker]; exact hc) hgc
    (by rw [hker]; exact hk) hg2
    (by rw [hker, _root_.Group.IsPerfect.commutator_eq_top, inf_top_eq]; exact hn)
    hgcard hdihedral
  let x' : _root_.commutator E := ⟨x, by rw [_root_.Group.IsPerfect.commutator_eq_top]; trivial⟩
  have hs : r x' ∈ center SL(2,ZMod 7) := involution_central _ (by
    rw [← map_pow]
    have he : x' ^ 2 = 1 := Subtype.ext hx
    rw [he, map_one])
  have hxc : x ∈ center E := by
    apply mem_center_iff.mpr
    intro y
    let y' : _root_.commutator E := ⟨y, by rw [_root_.Group.IsPerfect.commutator_eq_top]; trivial⟩
    have he := mem_center_iff.mp hs (r y')
    have he' : y' * x' = x' * y' := r.injective (by simpa only [map_mul] using he)
    exact congrArg Subtype.val he'
  have hfc : f x ∈ center SL(3,ZMod 2) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hxc z)
  rw [Atlas.Comparisons.Exceptional.sl3Two_center_eq_bot, mem_bot] at hfc
  exact hfx hfc
end BinaryLinearThree.CentralCover
