module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupTensor
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLineCubic

/-!
# The intrinsic tensor overgroup core argument

A cubic from the original component supplies the irreducible, fixed-free
action on the original tensor line. Thus the core and center argument needs
no separately chosen Cartan subgroup or cubic element. The earlier
omega-commutator containment and outside-overgroup hypotheses remain explicit.

Source: Aschbacher–Smith 9.3.6.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original component supplies the cubic action required by the overgroup core argument. -/
theorem outside_core_and_center_of_original_tensor
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    (H : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hLH : L ≤ H) (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hout : ¬ H ≤ D.maximalLocal) :
    m.tensorLine ≤ H.pCoreIn 2 ∧ H ∈ Chapter1.He G ∧
      generalizedFitting H = pCore 2 H ∧ center H = ⊥ := by
  obtain ⟨d,hdL,hd3,hdn,hdc⟩ := m.exists_tensorLine_cubic
  exact m.outside_core_and_center_of_original_tensor_cubic hn houtside hcomm H (zpowers d)
    hcore hLH hRH hout (zpowers_le.mpr (hLH hdL)) (zpowers_le.mpr hdn)
    d (mem_zpowers d) hd3 hdc
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
