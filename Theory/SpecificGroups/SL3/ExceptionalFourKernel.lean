module
public import Theory.SpecificGroups.SL3.PerfectCentralCover
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound
public import Theory.GroupTheory.CoveringComparisonKernelCard

/-!
# Kernel bounds for perfect central covers of full SL₃(4)

Compose the supplied cover with the scalar projection onto PSL₃ and lift
its canonical universal cover. The projective kernel has order dividing 48,
while the scalar kernel has order three. Thus the original kernel has order
dividing sixteen. It is a quotient of a Sylow two-subgroup of the canonical
kernel: the lift of that Sylow has both cube and fourth power one in SL₃.
The checked rank and exponent bounds therefore descend to the original kernel.

The application to intrinsic MS cores and their whole central and Frattini
actions is in LinearThreeMS.NonbinarySource.ExceptionalKernel. These bounds
do not assert that the exceptional kernel is trivial.
Source: Aschbacher--Smith I.1.3(6), printed p.407; GLS3 §6.1, Theorem 6.1.4.
The universal-cover bounds are proved in PSL3.ExceptionalFourCover.KernelBound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace Matrix.SL3.ExceptionalFourKernel
open Matrix.PSL3

private theorem full_cover_kernel_dvd {E F : Type*} [Group E] [Finite E]
    [Field F] [Finite F] (hF : Nat.card F = 4)
    (f : PerfectCentralCovering.Cover E SL(3,F)) :
    Nat.card f.toMonoidHom.ker ∣ 16 := by
  let : IsQuasisimple SL(3,F) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let := f.isQuasisimple
  let c := ExceptionalFourCover.coverOver F hF
  let g := (projectionCovering F).comp f.toCovering
  let a := (ExceptionalFourCover.coverOver_isUniversal F hF).lift g
  have ha : g.toMonoidHom.comp a.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom ((ExceptionalFourCover.coverOver_isUniversal F hF).lift_fac g)
  have hd := kernel_card_dvd_of_surjective_factor c.toMonoidHom g.toMonoidHom
    a.toMonoidHom a.surjective ha
  have hg := kernel_card_eq_mul_of_surjective_factor g.toMonoidHom
    (projection F) f.toMonoidHom (projection_surjective F) f.surjective rfl
  rw [ExceptionalFourCover.coverOver_ker] at hd
  have hh := hd.trans ExceptionalFourCover.kernel_card_dvd
  rw [hg,card_projectionKernel,hF] at hh
  norm_num at hh
  exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 3)).mp hh


private theorem full_cover_kernel_quotient {E F : Type*} [Group E] [Finite E]
    [Field F] [Finite F] (hF : Nat.card F = 4)
    (f : PerfectCentralCovering.Cover E SL(3,F)) :
    ∃ P : Sylow 2 ExceptionalFourCover.cover.toMonoidHom.ker,
      ∃ b : P →* f.toMonoidHom.ker, Function.Surjective b := by
  let : IsQuasisimple SL(3,F) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let := f.isQuasisimple
  let c := ExceptionalFourCover.coverOver F hF
  let g := (projectionCovering F).comp f.toCovering
  let a := (ExceptionalFourCover.coverOver_isUniversal F hF).lift g
  let k := f.toCovering.comp a
  have ha : g.toMonoidHom.comp a.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom ((ExceptionalFourCover.coverOver_isUniversal F hF).lift_fac g)
  have hk (y : ExceptionalFourCover.CoverGroup) :
      projection F (k y) = c y := DFunLike.congr_fun ha y
  let C := ExceptionalFourCover.cover.toMonoidHom.ker
  have hker : k.toMonoidHom.ker ≤ C := by
    intro y hy
    change y ∈ ExceptionalFourCover.cover.toMonoidHom.ker
    rw [←ExceptionalFourCover.coverOver_ker F hF]
    change c y = 1
    rw [←hk,show k y = 1 from hy,map_one]
  have hp : IsPGroup 2 k.toMonoidHom.ker :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 4)
      (full_cover_kernel_dvd hF (PerfectCentralCovering.ofCovering k))
  let : IsMulCommutative C := ⟨⟨fun x y => Subtype.ext
    (mem_center_iff.mp (ExceptionalFourCover.cover.ker_le_center x.property) y).symm⟩⟩
  let P : Sylow 2 C := Classical.choice inferInstance
  have hKP : k.toMonoidHom.ker.subgroupOf C ≤ P :=
    hp.comap_subtype.le_sylow_of_normal P
  have hPk (x : P) : k (x : C) = 1 := by
    have hxc : c ((x : C) : ExceptionalFourCover.CoverGroup) = 1 := by
      apply (ExceptionalFourCover.coverOver_ker F hF).ge
      exact (x : C).property
    have hxp : projection F (k (x : C)) = 1 := (hk _).trans hxc
    let z : (projection F).ker := ⟨k (x : C),hxp⟩
    have h3 : (k (x : C)) ^ 3 = 1 := by
      have hh := congrArg Subtype.val (pow_card_eq_one' (x := z))
      simpa only [Subgroup.coe_pow,Subgroup.coe_one,card_projectionKernel,hF,
        show Nat.gcd 3 (4-1) = 3 by decide] using hh
    have h4 : (k (x : C)) ^ 4 = 1 := by
      let t : P →* SL(3,F) := k.toMonoidHom.comp
        (C.subtype.comp (P : Subgroup C).subtype)
      have hh := congrArg t (ExceptionalFourCover.two_sylow_pow_four P x)
      simpa only [map_pow,map_one,t,MonoidHom.comp_apply,Subgroup.subtype_apply,
        Covering.toMonoidHom_apply] using hh
    simpa only [show 4 = 3+1 from rfl,pow_succ,h3,one_mul] using h4
  let b : P →* f.toMonoidHom.ker :=
    ((a.toMonoidHom.comp C.subtype).comp (P : Subgroup C).subtype).codRestrict
      f.toMonoidHom.ker hPk
  refine ⟨P,b,?_⟩
  intro x
  obtain ⟨y,hy⟩ := a.surjective x.val
  change a y = x.val at hy
  have hyk : y ∈ k.toMonoidHom.ker := by
    change f.toMonoidHom (a y) = 1
    rw [hy]
    exact x.property
  let yC : C := ⟨y,hker hyk⟩
  exact ⟨⟨yC,hKP hyk⟩,Subtype.ext hy⟩

/-- Every finite perfect central cover of full SL₃ over a field of order four
has kernel of order dividing sixteen, generator rank at most two and exponent
dividing four. The kernel is that of the supplied covering map. -/
theorem kernel_bounds {E F : Type*} [Group E] [Finite E]
    [Field F] [Finite F] (hF : Nat.card F = 4)
    (f : PerfectCentralCovering.Cover E SL(3,F)) :
    Nat.card f.toMonoidHom.ker ∣ 16 ∧ Group.rank f.toMonoidHom.ker ≤ 2 ∧
      ∀ x : f.toMonoidHom.ker, x ^ 4 = 1 := by
  obtain ⟨P,b,hb⟩ := full_cover_kernel_quotient hF f
  refine ⟨full_cover_kernel_dvd hF f,
    (Group.rank_le_of_surjective b hb).trans (ExceptionalFourCover.two_sylow_rank_le_two P),?_⟩
  intro x
  obtain ⟨y,rfl⟩ := hb x
  rw [←map_pow,ExceptionalFourCover.two_sylow_pow_four P y,map_one]

end Matrix.SL3.ExceptionalFourKernel
