module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.WreathedCatalogue
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.WreathedResidual

/-!
# Literal F.6 row (10) from its original wreathed source

The original two-residual and quasisimple component hypotheses, together
with the actual wreathed Sylow, force the component to be the whole group.
The complete source catalogue then supplies the linear or unitary cover,
prime and modulo-eight sign. The conclusion retains the original local
extension maps; no ambient-equality or model-selection premise remains.

Source: Aschbacher--Smith F.6.18(10), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

/-- Row (10), with source residual, ambient equality, model, and cover steps discharged. -/
theorem ten_of_wreathed_source
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hH : IsSQTK κ H) (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G)
    (S : Sylow 2 G) (hsylow : Nonempty (S ≃* W32))
    (hleft : CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (Equiv.Perm (Fin 3))) : Alternative G₁ G₂ S := by
  exact ten_of_wreathed_source_component_top hA hC hH eG hK
    (component_top_of_wreathed_source hA hC hH eG hK hres S (Classical.choice hsylow))
    S hsylow hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
