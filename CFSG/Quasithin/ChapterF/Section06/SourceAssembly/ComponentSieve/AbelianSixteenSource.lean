module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.AbelianSixteen
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentModels

/-!
# The original component quotient has no C4 times C4 Sylow

The genuine earlier A/C results classify the literal central quotient of
the supplied component in the original SQTK quotient. Applying the full
carrier sieve excludes the abelian-sixteen Sylow without any separately
assumed model list. This is the proper-residual elimination in the
wreathed branch of Aschbacher--Smith F.6.18(10), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.AbelianSixteen
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {K : Subgroup G}

theorem not_component_central_quotient_sylow
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (P : Sylow 2 (K ⧸ center K))
    (eP : P ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) : False := by
  exact not_theoremC_model P eP (component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK)

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.AbelianSixteen
