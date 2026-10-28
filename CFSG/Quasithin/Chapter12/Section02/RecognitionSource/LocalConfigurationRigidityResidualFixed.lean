module
public import Theory.GroupAction.BinarySubspaceResidual
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelComplete

/-!
# The hyperplane residual fixed space and component core in 12.2.25

Write W=U∩V, R=C_T(U), Y=O²(N_L(W)), and Z=C_T(L). The full natural
action induces every automorphism of W in N_L(W). Hence C_W(Y)=1:
a nontrivial residual-fixed normal two-subgroup would contain a point
centralized by the whole normalizer. The three-subgroups lemma then shows
that C_R(Y) centralizes V. The already proved kernel splitting identifies
this fixed space with Z, with all subgroups and residual maps unchanged.

Separately, the disjoint Sylow splitting T=(T∩L)×Z and C_T(V)=V×Z put
O₂(L) inside V, so O₂(L)=V in every source dimension. The final source
applications discharge the shared centralizer record. The normalizer/action
application removes its former fixed-space premise; normality of Y in N_G(R)
remains with this task, qt-d-12213-local-rigidity, along with the transfer,
dimension cutoff and actual parabolic-factor construction.

Source: Aschbacher--Smith, original 12.2.25, printed pp.805--806.
These results do not assert completion of 12.2.25--26.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityResidual
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

omit [Finite G] in
theorem hyperplane_index
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V : Subgroup G).relIndex V = 2 := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,C.hyperplane,RigidityKernel.chosen_card A] at hh
  have hd : d = (d-1)+1 := by have := A.dimension.1; omega
  have hpow : 2 ^ d = 2 ^ (d-1) * 2 := by
    conv_lhs => rw [hd]
    rw [pow_succ]
  rw [hpow] at hh
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by decide) _) hh

omit [Finite G] in
theorem hyperplane_full (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) :
    Function.Surjective ((U ⊓ V : Subgroup G).normalizerMonoidHom.comp
      (inclusion (show L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G) ≤
        normalizer ((U ⊓ V : Subgroup G) : Set G) from inf_le_right))) := by
  let := D.elementary
  exact BinarySubspaceResidual.stabilizer_full L V (U ⊓ V) D.normalizes inf_le_right
    (A.componentAut_surjective D)

theorem hyperplane_residual_fixed_eq_bot (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V) ⊓ centralizer (rigidityHyperplaneResidual L U V : Set G) = ⊥ := by
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  let W := U ⊓ V
  let := D.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (show W ≤ V from inf_le_right)) (inclusion_injective _)
  have hc : 2 < Nat.card W := by
    rw [show Nat.card W = 2 ^ (d-1) from C.hyperplane]
    have hd : 1 < d-1 := by have := A.dimension.1; omega
    exact lt_of_eq_of_lt (by decide : 2 = 2^1) (pow_lt_pow_right₀ (by decide) hd)
  apply BinarySubspaceResidual.residual_fixed_eq_bot F W
    (le_inf (inf_le_right.trans D.le_component) W.le_normalizer) inf_le_right
  exact BinarySubspaceResidual.fixed_eq_bot F W inf_le_right hc (hyperplane_full D A)

/-- The literal residual fixed space, in all three source dimensions. -/
theorem radical_fixed_eq_component_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (rigidityHyperplaneResidual L U V : Set G) =
        (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let W := U ⊓ V
  let Y := rigidityHyperplaneResidual L U V
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let X := R ⊓ centralizer (Y : Set G)
  have hYL : Y ≤ L := (map_subtype_le _).trans inf_le_left
  have hYW : Y ≤ normalizer (W : Set G) := (map_subtype_le _).trans inf_le_right
  have hYV : Y ≤ normalizer (V : Set G) := hYL.trans D.normalizes
  have hTV := ((structural G T L h).2.2 V D).1
  have hRW : R ≤ centralizer (W : Set G) := inf_le_right.trans (centralizer_le inf_le_left)
  have hRV : R ≤ normalizer (V : Set G) := inf_le_left.trans hTV
  have hVY : ⁅V,Y⁆ ≤ W := commutator_le_of_normalized_index_two V W Y
    inf_le_right (hyperplane_index A C) hYV hYW
  have hVR : ⁅V,R⁆ ≤ W := commutator_le_of_normalized_index_two V W R
    inf_le_right (hyperplane_index A C) hRV
    (hRW.trans (Subgroup.centralizer_le_normalizer _))
  have hXY : ⁅Y,X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp inf_le_right)
  have hVYX : ⁅⁅V,Y⁆,X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hVY.trans (le_centralizer_iff.mp (inf_le_left.trans hRW)))
  have hXVY : ⁅⁅X,V⁆,Y⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hVYX
    (by rw [hXY, commutator_bot_left])
  have hXVW : ⁅X,V⁆ ≤ W := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_left).trans hVR
  have hXV : ⁅X,V⁆ = ⊥ := bot_unique ((le_inf hXVW
    (commutator_eq_bot_iff_le_centralizer.mp hXVY)).trans_eq
      (hyperplane_residual_fixed_eq_bot D A C))
  have hZX : Z ≤ X := le_inf
    (le_sup_right.trans B.centralizer_split.symm.le)
    (inf_le_right.trans (centralizer_le hYL))
  have hZV : Z ≤ centralizer (V : Set G) :=
    inf_le_right.trans (centralizer_le D.le_component)
  have hZY : Z ≤ centralizer (Y : Set G) := inf_le_right.trans (centralizer_le hYL)
  have hsplit : R ⊓ centralizer (V : Set G) = Z ⊔ W := by
    rw [show R = U ⊔ Z from B.centralizer_split, sup_comm,
      inf_centralizer_sup_of_centralizing Z U V
        ((le_sup_right.trans B.centralizer_split.symm.le).trans
          (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))) hZV,
      C.action_kernel]
  have hXZW : X ≤ Z ⊔ W := (le_inf inf_le_left
    (commutator_eq_bot_iff_le_centralizer.mp hXV)).trans hsplit.le
  have hfix : (Z ⊔ W) ⊓ centralizer (Y : Set G) = Z := by
    rw [inf_centralizer_sup_of_centralizing Z W Y
      ((hZV.trans (centralizer_le inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)) hZY,
      hyperplane_residual_fixed_eq_bot D A C, sup_bot_eq]
  exact le_antisymm ((le_inf hXZW inf_le_right).trans hfix.le) hZX

omit [Finite G] in
/-- The completed Sylow splitting already identifies the original component core. -/
theorem component_core_of_centralizers
    (D : ChosenModule T L V) (B : LocalRigidityCentralizers T L V U P) :
    L.pCoreIn 2 = V := by
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hcorejoin : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hcoreT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply hcorejoin.trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hcoreVZ : L.pCoreIn 2 ≤ V ⊔ Z :=
    (le_inf hcoreT (hcorejoin.trans D.core_centralizes)).trans B.kernel_split.le
  have hVZ : V ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le D.le_component))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm ?_ D.le_componentCore
  intro x hx
  have hprod : x ∈ (V : Set G) * (Z : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right V Z hVZ]
    exact hcoreVZ hx
  obtain ⟨v,hv,z,hz,rfl⟩ := hprod
  have hzL : z ∈ L := by
    have hh := L.mul_mem (L.inv_mem (D.le_component hv)) (pCoreIn_le 2 L hx)
    simpa only [inv_mul_cancel_left] using hh
  have hz1 := disjoint_def.mp B.sylow_disjoint ⟨hz.1,hzL⟩ hz
  change v * z ∈ V
  rw [hz1, mul_one]
  exact hv

/-- Source application with the shared centralizer calculation discharged. -/
theorem source_component_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) : L.pCoreIn 2 = V :=
  component_core_of_centralizers D (RigidityKernel.source_centralizers h D structural A C hnone)

/-- The original fixed-space identity has no additional component or tensor input. -/
theorem source_radical_fixed_eq_component_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (rigidityHyperplaneResidual L U V : Set G) =
        (T : Subgroup G) ⊓ centralizer (L : Set G) :=
  radical_fixed_eq_component_centralizer h D structural A C
    (RigidityKernel.source_centralizers h D structural A C hnone)

/-- Application to the existing normalizer/action consumer. Only residual
normality remains for the component argument owned by qt-d-12213-local-rigidity. -/
theorem source_normalizer_action_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ∃ a : HigherRigidity.NormalizerQuotient U →* MulAut U,
        Function.Injective a ∧ ∀ (g : normalizer (U : Set G)) (u : U),
          (a (HigherRigidity.quotient U g) u : G) = (g : G) * (u : G) * (g : G)⁻¹ :=
  RigidityKernel.source_higher_normalizer_action_of_residual_normal h D structural A C hnone hn
    (source_radical_fixed_eq_component_centralizer h D structural A C hnone)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityResidual
