module
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.Assembly

/-!
# Earlier source data for the rank-two terminal action

This record selects only the quotient, kernel, stabilizer and center clauses
of 12.8.9--10 needed to apply 12.8.11 and G.10 to the original rank-two flag.
The source owner constructs these fields from the preceding parabolic
calculations; no terminal recognition or transvection conclusion is assumed.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- The earlier parabolic and center clauses used by the rank-two terminal action. -/
structure TerminalEarlierData (F : InvariantFlag T V 2) (g : G) (hg : g ∈ F.Gi 2) : Prop where
  quotient_normal : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal
  quotient_elementary : letI := quotient_normal
    IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸
      (F.E g).subgroupOf (F.W ⊔ F.X g))
  disjoint : Disjoint (conjugate (F.Vi 1) g) F.ZU
  kernel : F.xHatKernel g hg = F.E g
  stabilizer : ∀ u : F.U, (u : G) ∉ F.W →
    (F.xHatStabilizer g hg (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
      (conjugate F.ZU g : Set G) * (F.E g : Set G)
  center_cut : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1
  conjugate_center_cut : conjugate F.ZU g ⊓ F.U =
    (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
