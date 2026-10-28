module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.CentralQuotientFive
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.Source

/-!
# The original A₅ setup from the natural central quotient

Projectivity reconstructs the same chosen V from the central-quotient
alternative of 12.2.2(3d). Homogeneity then gives its T-invariance, and the
existing flag construction supplies the actual A₅ Context. Its local
application gives reducedness and C_T(V)=O₂(LT).

Neither a splitting, a full-module marking, an invariant flag nor an
A₅ Context is assumed. The earlier classification identifying the
central quotient remains explicit and must be proved in final assembly.

Source: Aschbacher--Smith, 12.2.2(3d), 13.3.2(3), Notation 13.2.1 and
13.2.3(1), printed pp.795, 885, and 877--878.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The central quotient of the literal chosen subspace constructs the
original Context and its entire invariant flag. -/
theorem exists_context_of_natural_central_quotient
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (a : d.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (ha : ∀ (l : L) v, a (d.chosenCentralAction l v) =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v)) :
    ∃ V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      Nonempty (Section05.A5Source.Context T L V V₁ V₂ V₃) :=
  exists_context_of_one_or_two_modules h d
    (Or.inl (d.a5_model_of_central_quotient e a ha))

/-- The same central-quotient marking supplies the reducedness and exact
local two-core equality used by the original F.9 setup. -/
theorem local_setup_of_natural_central_quotient
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (a : d.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (ha : ∀ (l : L) v, a (d.chosenCentralAction l v) =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v)) :
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      (T : Subgroup G) ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  local_setup_of_one_or_two_modules h d
    (Or.inl (d.a5_model_of_central_quotient e a ha))

end CFSG.Quasithin.Chapter13.Section03.A5Setup
