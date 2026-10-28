module
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.RootCentralizer
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.SylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Cubic rank of pointwise Sylow fixers in even G₂

The proved inner-field description makes the original Sylow-fixing
involution inner by a long-root element. Its full centralizer is the
actual first local group. The latter's SL₂ projection has a two-group
kernel, bounding its cubic rank by one. Every conjugation and fixed-group
comparison uses the same automorphism and field.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832, using the
root-centralizer and automorphism calculations of F.1.12 and 16.1.6.
-/
public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2
open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The first local group's literal SL₂ quotient bounds its cubic rank. -/
theorem firstLocal_threeRank_le_one : primeRank 3 (local₁ (F := F)) ≤ 1 := by
  have hp : IsPGroup 2 (shortSLHom (F := F)).ker := by
    rw [shortSLHom_ker]
    let j : radical₁.subgroupOf local₁ →* unipotent (K := F) :=
      { toFun x := ⟨x.val.val, fiveRootSubgroup_le_unipotent 5 (Or.inr rfl) x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    apply (sylow (F := F)).isPGroup'.of_injective j
    intro x y h
    have he : x.val.val = y.val.val :=
      congrArg (fun z : unipotent (K := F) => z.val) h
    exact Subtype.ext (Subtype.ext he)
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  exact (primeRank_le_of_coprime_ker 3 shortSLHom (by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k)).trans
      (Matrix.SL2.binary_odd_primeRank_le_one (by decide : Odd 3))

/-- The original Sylow-fixing involution has fixed-group cubic rank at most one. -/
theorem sylow_fixer_fixed_threeRank_le_one (hF : 2 < Nat.card F)
    (P : Sylow 2 (Model F)) (a : MulAut (Model F)) (ha : orderOf a = 2)
    (hfix : ∀ x ∈ P, a x = x) : primeRank 3 a.fixedSubgroup ≤ 1 := by
  obtain ⟨x,_,he,⟨g,t,ht,hx⟩⟩ := EvenInvolutionGeometry.fixing_sylow_involution_longRoot hF
    (LieAutomorphismExtensions.semilinearAction_bijective hF).2 P a hfix
    (by simpa only [ha] using pow_orderOf_eq_one a) (by intro h; simp [h] at ha)
  rw [he,MulAut.fixedSubgroup_conj,hx]
  let e := CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) (rootA t)
  rw [←primeRank_equiv 3 e,centralizer_rootA_eq_local₁ ht]
  exact firstLocal_threeRank_le_one
end Atlas.G2
