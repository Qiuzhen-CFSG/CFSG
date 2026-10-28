module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedKernelSource
public import Theory.Representation.NormalComponentConstituents.ElementaryKernel

/-!
# Elementary Sylow subgroups in the original paired branch

The already proved separation of the two actual exchanged constituent actions
makes the intersection of the original point Sylow with the literal kernel
elementary abelian. Noncentrality of that kernel supplies an actual conjugate
of L inside it. Sylow restriction and conjugacy then give elementary Sylow
two-subgroups of the original L, retaining the same chosen constituent and all
original ambient hypotheses. Paired-A5 recognition is a later obligation.

Source: Aschbacher--Smith G.10.15, printed p.362; 14.3.12--15,
printed pp.993--994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedPairedSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedPairedSource T M Mc F g B v L I)

include s

/-- The literal original Sylow meets the chosen constituent kernel in an
elementary abelian two-group. -/
theorem kernel_sylow_elementary :
    let H := componentOrbit L ⊤
    let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
    IsElementaryAbelian 2
      ((((pointSylow (F:=F):Subgroup F.TerminalHdot).subgroupOf H) ⊓
        R.toRepresentation.asGroupHom.ker) : Subgroup H) := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  obtain ⟨x,_,hsep⟩ := s.pair_separates
  exact Representation.BinaryOffender.ExchangedKernel.kernel_sylow_elementary F.terminalRepresentation H
    (F.terminalDot (F.X g)) (pointSylow (F:=F)) s.actor_sylow.2
    (invariantSubspace F.terminalRepresentation H I s.selected.invariant) x hsep

/-- Every Sylow two-subgroup of the original moved component is elementary
abelian in the noncentral-kernel branch. No component-image recognition is
assumed. -/
theorem component_sylow_elementary (P : Sylow 2 L) : IsElementaryAbelian 2 P := by
  let N := (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤)
    I s.selected.invariant).toRepresentation.asGroupHom.ker
  let : IsElementaryAbelian 2
      ((((pointSylow (F:=F):Subgroup F.TerminalHdot).subgroupOf (componentOrbit L ⊤)) ⊓ N) :
        Subgroup (componentOrbit L ⊤)) := s.kernel_sylow_elementary
  exact Representation.BinaryOffender.ExchangedKernel.component_sylow_elementary_of_kernel s.component
    (pointSylow (F:=F)) N s.noncentral_kernel P

end ExchangedPairedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
