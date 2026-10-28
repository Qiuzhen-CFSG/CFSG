module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Models
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.SylowSections
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction

/-!
# The J₃ model gate on the original selected component

The component is inside the literal N(A), so its possible central cover
and its original outer action are retained. The certified Sylow bound
excludes the nonsolvable simple L_A section (whose order has a factor 27)
from this outer group. No ambient SQTK or independent model geometry is used.
Source: Aschbacher–Smith 4.4.3, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]

theorem selected_jankoThree_no_large_cubic_outer_section
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hmodel : Nonempty (K ⧸ center K ≃* Sporadic.Janko3.Model))
    (hS : ¬ Group.IsSolvable S) (h27 : 27 ∣ Nat.card S)
    (U : Subgroup (MulAut.Outer K)) (f : U →* S) (hf : Function.Surjective f) : False := by
  let : IsQuasisimple K := hK.2
  obtain ⟨e⟩ := hmodel
  exact ChapterA.Section03.SourceComponents.TheoremBOuter.jankoThree_cover_no_large_cubic_simple_section
    e hS h27 U f hf
/-- The literal G₂(2)′ model supplied by the original L_A quotient is excluded. -/
theorem selected_jankoThree_no_binaryDerived_outer_section
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hmodel : Nonempty (K ⧸ center K ≃* Sporadic.Janko3.Model))
    (U : Subgroup (MulAut.Outer K))
    (f : U →* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Surjective f) : False := by
  let S := commutator (Atlas.G2.Model (ZMod 2))
  let : IsSimpleGroup S := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect S := by
    change Group.IsPerfect Atlas.G2.LieAutomorphismExtensions.BinaryDerived
    rw [Atlas.G2.LieAutomorphismExtensions.binaryDerived_eq]
    exact Atlas.G2.BinaryException.H_isPerfect
  exact selected_jankoThree_no_large_cubic_outer_section A K hK hmodel
    (Group.IsPerfect.not_isSolvable S)
    (by change 27 ∣ Nat.card Atlas.G2.LieAutomorphismExtensions.BinaryDerived
        rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]; norm_num) U f hf
end CFSG.Quasithin.Chapter4.Section04
