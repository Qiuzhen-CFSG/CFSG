module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationProductsKernel
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationProductsResidual

/-!
# The two centralizer products of the marked fifth MS alternative

On the original chosen module, kernel centralization and the H¹ correction
give C_T(V) = V C_T(L). The literal embedded residual O²(C_L(E)) fixes
exactly E in V, and its centralizer in R centralizes V. Restricting the first
product therefore gives C_R(L₁) = E C_T(L). All three calculation premises
of the earlier reduction are discharged by the kernel and residual proofs.

The products require no normalization of L₁ by N_G(R). That separate
fixed-branch hypothesis is used only in the final application to the existing
Frattini consumer, which proves C_T(V) = V and C_T(L) = C_V(L).

The genuine fifth alternative, its quotient marking, and msQ = V are the
explicit inputs produced by `qt-d-1246-l3-ms-specialization`, which retains
the full source assembly and discharge of those inputs. Structural1222 and
SLThreeAlternative1222 remain the authorized earlier Section 12.2 premises.
In particular, msQ = [O₂(LR),L] = V is not O₂(LR) = C_T(V).

Source: Aschbacher--Smith, proof of 12.4.6, printed pp.813--814;
C.1.31--34, pp.135--137, and B.4.8, pp.91--92.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- Both original centralizer products after selection of the genuine fifth
MS alternative. No kernel, residual-action or product premise remains. -/
theorem ms_fixedBlockIdentities
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    FixedBlockIdentities d := by
  have hproduct := d.ms_core_product h structural marked hmodel hne hescape e hcase hQ
  exact ⟨hproduct,
    d.ms_residual_centralizer_product h structural marked hmodel hne hescape hproduct⟩

/-- Apply the proved products to the original fixed-residual consumer.
Only this application requires N_G(R) to normalize the literal L₁. -/
theorem ms_selfCentralizing_of_fixed_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = V ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = fixedSubgroup L V := by
  have b := d.ms_fixedBlockIdentities h structural marked hmodel hne hescape e hcase hQ
  exact fixedBlock_selfCentralizing h structural marked hmodel hne d hescape hline
    b.product b.residual_centralizer

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
