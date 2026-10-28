module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionSupplement.ThompsonMovement
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionSupplement.Commutator
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockMSIndependentApplication
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockActionSource
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionLineAction
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionInverter

/-!+# The original L₃(2) fixed-involution fusion branch

Thompson movement on the original omega module gives its B.5.1 commutator
bound. The fixed supplement then constructs the actual invariant plane and
local Sylow subgroup. In the escaping-normalizer cases, the independent
C.1.34 specialization and fixed-plane action give the two-member maximum
elementary family, while the actual centralizing quotient line and Sylow
inverter give the corrected moving-residual contradiction.

Thus all three local inputs to the Sylow and fusion assembly are discharged.
Only the structural and marked-module implications of Section 12.2 remain
explicit; their source producers are `qt-d-1222-source` and
`qt-d-1222-modules`. No universal MS classification, local geometry witness,
residual calculation or Thompson-movement premise is assumed here.

Source: Aschbacher–Smith, 12.4.5–7, printed pp.813–814. The product in
12.4.5(2) contains the whole V, and the weak closure in 12.4.7 concerns V.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u

/-- The original B.5.1 commutator calculation, with Thompson movement proved
from the ambient source hypotheses. -/
theorem omegaCommutatorCalculation_of_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    OmegaCommutatorCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  exact omega_commutator_le_of_thompson_movement D h E
    ((structural G T L h).2.2 V D).1 hne
    (thompson_moves_omega_center_of_source h D structural marked hmodel hne)

/-- The fixed supplement in the original omega module, with its commutator
and Thompson premises discharged. -/
theorem fixedSupplementCalculation_of_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    FixedSupplementCalculation.{u} :=
  fixedSupplement_of_omegaCommutator structural marked
    (omegaCommutatorCalculation_of_source structural marked)

/-- Construct the actual source plane, nonfixed point, fixed space, index
and local Sylow witness, with no local calculation left as an input. -/
theorem localCalculations_of_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    LocalCalculations.{u} :=
  localCalculations_of_fixedSupplement structural marked
    (fixedSupplementCalculation_of_source structural marked)

/-- The fixed-residual contract from the original block and its actual
action, retaining only the earlier Section 12.2 implications. -/
theorem fixedResidualCalculation_of_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    FixedResidualCalculation.{u} :=
  fixedResidualCalculation_without_binary_and_action structural marked
    (fixedBlockActionCalculation structural marked)

/-- The moving-residual contract from the corrected normal-residual
contradiction, with the block, centralizing line and inverter all supplied. -/
theorem movingResidualCalculation_of_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    MovingResidualCalculation.{u} :=
  movingResidualCalculation_without_binary_and_actions structural marked
    (movingCentralizingLineCalculation structural marked)
    (movingInverterCalculation structural marked)

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 12.4.5(1–2): Z centralizes L and Ω₁Z(C_T(V)) is Z times the
whole original V. The plane used to prove this is constructed internally. -/
theorem omega_center_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    omegaCenterIn (T : Subgroup G) ≤ centralizer (L : Set G) ∧
      omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
        omegaCenterIn (T : Subgroup G) ⊔ V := by
  obtain ⟨d⟩ := localCalculations_of_source structural marked G T L V h D hmodel hne
  have hfixed : omegaCenterIn (T : Subgroup G) ⊓ V ≤ centralizer (L : Set G) := by
    rw [d.fixed_line h structural marked hmodel hne]
    exact inf_le_right
  have hc := omega_center_of_fixed_supplement D d.E d.le_module
    d.fixed_supplement hfixed d.fixed_plane
  exact ⟨hc.1, hc.2.1⟩

/-- Source 12.4.6 for the original C_T(E), including its index two in T.
Both escaping-normalizer alternatives and the local geometry are proved. -/
theorem sylow_witness_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ (E : Subgroup G) (v : G), E ≤ V ∧ Nat.card E = 4 ∧ v ∈ E ∧
      v ∉ fixedSubgroup L V ∧
      ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (E : Set G))
        (centralizer ({v} : Set G)) :=
  sylow_witness_of_calculations h D structural marked hmodel hne
    (localCalculations_of_source structural marked)
    (fixedResidualCalculation_of_source structural marked)
    (movingResidualCalculation_of_source structural marked)

/-- The original L₃(2) branch of 12.4.7, including the fixed involution,
its centralizer containment, weak closure in V and L-controlled fusion. -/
theorem fusion_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
      ∀ x ∈ V, ∀ y ∈ V, IsConj x y → ∃ l ∈ L, MulAut.conj l x = y :=
  fusion_of_calculations h D structural marked hmodel hne
    (localCalculations_of_source structural marked)
    (fixedResidualCalculation_of_source structural marked)
    (movingResidualCalculation_of_source structural marked)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
