module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupCharacteristic

/-!
# Characteristic two from the original tensor singular line

Apply the original overgroup criterion to the literal four-element tensor
line. Its T-central involution and the bound C_T(V₂) ≤ N_T(L) are now proved
from the chosen tensor coordinates. Only the original overgroup premises,
including containment of the line in O₂(H), remain explicit.

Source: Aschbacher–Smith 9.3.6, combined manuscript, printed p.733.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem outside_characteristicTwo_of_tensorLine_core
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hLH : L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hout : ¬ H ≤ D.maximalLocal)
    (hU : m.tensorLine ≤ H.pCoreIn 2) :
    H ∈ Chapter1.He G ∧ generalizedFitting H = pCore 2 H := by
  obtain ⟨z,hz,hzU,hzc⟩ := m.exists_central_involution_tensorLine
  exact source_a5_outside_characteristicTwo_of_tensor_core D e hn H m.tensorLine
    hcore hLH hRH hout hU m.sylow_centralizer_tensorPlane_le_stabilizer z hz hzU hzc

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
