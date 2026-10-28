module

public import Theory.GroupTheory.CComponent.OrbitExhaustion
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation

/-!
# The generated-group Sylow orbit assertion of A.3.8(3)

The proved A.3.7 commutation theorem supplies the orbit-exhaustion argument.
The actual generating component, ambient Sylow subgroup, SQTK hypothesis,
and trivial two-core are retained; no orbit or normality premise remains.

Source: Aschbacher–Smith, A.3.8(3), printed p.45.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
theorem sylow_orbit_of_generated (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) {X B : Subgroup G} (hX : X.IsCComponent)
    (hgen : X ⊔ S = ⊤) (hB : B.IsCComponent) :
    ∃ s : S, B = X.map (MulAut.conj (s : G)).toMonoidHom :=
  hX.conjugate_of_pGroup_generated_of_commuting hB S.isPGroup' hgen
    (fun _ hC hne => CComponentCommutation.commutator_eq_bot hG hO hB hC hne)
end CFSG.Quasithin.ChapterA.Section03.SourceComponents
