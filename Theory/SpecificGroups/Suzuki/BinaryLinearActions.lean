module
public import Theory.SpecificGroups.Suzuki.SchurEightUpper.KernelGeneration.SuzukiActions
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.SpecificGroups.PSL2.BinaryOuter
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.GroupTheory.PerfectSimpleImage

/-!
# Perfect Suzuki covers acting on binary projective line groups

A subgroup of binary PSL₂ has abelian Sylow two-subgroups. Surjections
preserve Sylow subgroups, so its sections cannot be Suzuki groups, whose
root Sylows are nonabelian. Every nontrivial image of a perfect Suzuki
cover would retain that simple section. Finally the soluble outer quotient
puts a perfect automorphism image inside the inner group.

This proves triviality of the actual action homomorphism; it does not
assume the acting cover is an ambient component.
Source application: Aschbacher–Smith 5.1.16(2), printed p.639,
refs/quasithin.pdf. Model inputs: Huppert–Blackburn III XI.3.1–3.6
and the binary PSL₂ automorphism theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.Suzuki.BinaryLinearActions
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The nonabelian Suzuki root Sylow cannot be a section of binary PSL₂. -/
theorem no_suzuki_section {m : ℕ} (hm : 0 < m)
    (U : Subgroup PSL(2,F)) (f : U →* SuzukiMatrixGroup m) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨R,hR⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨P,hP⟩ := Sylow.mapSurjective_surjective hf 2 R
  let : IsMulCommutative P :=
    Theory.PSL2.binary_sylow_commutative_of_injective U.subtype U.subtype_injective P
  have hc : IsMulCommutative ((P : Subgroup U).map f) := map_isMulCommutative _ _
  have he : (P : Subgroup U).map f = SuzukiRootSubgroup m :=
    (congrArg (fun S : Sylow 2 (SuzukiMatrixGroup m) => (S : Subgroup (SuzukiMatrixGroup m))) hP).trans hR
  exact SchurCover.EightLocal.KernelActions.root_not_isMulCommutative m hm (he ▸ hc)

/-- Every perfect Suzuki cover acts trivially on a binary projective line group. -/
theorem perfect_cover_action_trivial {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {m : ℕ} (hm : 0 < m) (q : K →* SuzukiMatrixGroup m)
    (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (a : K →* MulAut PSL(2,F)) : a = 1 := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsSolvable (MulAut.Outer PSL(2,F)) :=
    Theory.PSL2.binary_outer_isSolvable_of_mulEquiv F (MulEquiv.refl _)
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hinner := MulAut.perfect_subgroup_le_inner a.range
  let b : K →* MulAut.innerSubgroup PSL(2,F) :=
    a.codRestrict _ (fun x => hinner ⟨x,rfl⟩)
  have hz : center PSL(2,F) = ⊥ := Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot
  let e : PSL(2,F) ≃* MulAut.innerSubgroup PSL(2,F) :=
    MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)
  have hb := hom_eq_one_of_no_simple_section q hq (no_suzuki_section hm)
    (e.symm.toMonoidHom.comp b)
  apply MonoidHom.ext
  intro x
  have hh := DFunLike.congr_fun hb x
  change e.symm (b x) = 1 at hh
  have hh' : b x = 1 := e.symm.injective (hh.trans e.symm.map_one.symm)
  exact congrArg Subtype.val hh'
end Theory.Suzuki.BinaryLinearActions
