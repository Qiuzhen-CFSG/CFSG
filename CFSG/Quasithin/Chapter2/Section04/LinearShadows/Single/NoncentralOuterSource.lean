module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionSource

/-!
# The even-field outer-action contradiction

The literal complement to the original Thompson subgroup cannot act on the
symplectic component as in 2.4.23(5): the involution restriction marks force it
to be cyclic, contrary to the original strong-closure consequence of 2.4.22.
The component recognition and the marked conjugation action remain explicit
inputs here; the final source consumer must construct them.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
variable {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G} {n m : ℕ}
/-- The literal original torus complement cannot have the even-field
symplectic action supplied by 2.4.23(5). Its prior fusion theorem already
forbids cyclicity, so all geometric obligations are explicit action marks. -/
theorem CyclicTorusSetup.false_of_even_symplectic_action
    (c : CyclicTorusSetup d T n) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hcard : Nat.card F=2^m) (hm : 1<m) (heven : Even m)
    (α : ((normalizer (c.hall : Set G)).subgroupOf (T : Subgroup G)) →* MulAut (Sp F))
    (hker : Nat.card ((QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp α).ker=2)
    (hloc : ∀ t, orderOf t=2 →
      QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) (α t) ≠ 1 →
      (∃ h : pointLocal.map (α t).toMonoidHom = pointLocal,
        pointSL2Action hcard hm (α t) h ∈
          MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (∃ h : planeLocal.map (α t).toMonoidHom = planeLocal,
        planeSL2Action hcard hm (α t) h ∈
          MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F))) : False := by
  let A := (normalizer (c.hall : Set G)).subgroupOf (T : Subgroup G)
  let : IsCyclic A := cyclic_of_outer_kernel_two_and_local_involutions
    hcard hm heven (T.isPGroup'.to_subgroup A) α hker hloc
  let := c.normal_in_sylow
  exact c.quotient_not_cyclic_of_fusion hG hclosed
    ((c.split_ambient.symm.QuotientMulEquiv).isCyclic.mpr inferInstance)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
