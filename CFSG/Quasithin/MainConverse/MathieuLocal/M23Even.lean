module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.SylowLocalCentralizerCriterion
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport

/-!
# Even characteristic of the concrete Mathieu group M23

The actual involution centralizer has a normal binary kernel of order sixteen
whose centralizer lies in that kernel. Thus its two-core is self-centralizing.
The checked involution fusion transports this conclusion to every involution
of the concrete design automorphism group.

Every two-local M containing a Sylow two-subgroup T has nontrivial two-core.
That core meets Z(T) in an involution z. The group C_M(z) contains the full
Sylow subgroup T of C_M23(z), so inherits characteristic two. Since it also
contains C_M(O₂(M)), the core-centralizer criterion proves characteristic two
in M. This covers all the required maximal two-locals without a subgroup
catalogue or an assumption about their cores.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4, and the repeated
statement on pp.481–482; the involution geometry is 5.2.21, printed p.657.
-/

public section

namespace CFSG.Quasithin.MainConverse

open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M23Geometry.InvolutionCentralizer

/-- Every involution centralizer in the actual M23 has a self-centralizing
two-core, using the embedded normal binary kernel. -/
theorem m23_involutionCentralizer_characteristicTwo {t : M23} (ht : orderOf t = 2) :
    HasCharacteristicTwo (centralizer ({t} : Set M23)) := by
  have hk : kernel ≤ pCore 2 representativeCentralizer :=
    le_sSup ⟨inferInstance, kernel_isTwoGroup⟩
  have hc : HasCharacteristicTwo representativeCentralizer :=
    (centralizer_le hk).trans (kernel_selfCentralizing.trans hk)
  obtain ⟨e⟩ := centralizer_equiv_representative ht
  exact hc.of_equiv e.symm

/-- Exhaustive local assertion: every two-local containing a full Sylow
two-subgroup of M23 has its actual two-core self-centralizing. -/
theorem m23_twoLocal_characteristicTwo (T : Sylow 2 M23) (M : Subgroup M23)
    (hM : IsTwoLocal M) (hTM : (T : Subgroup M23) ≤ M) :
    HasCharacteristicTwo M := by
  obtain ⟨Q, hne, hp, rfl⟩ := hM
  apply normalizer_core_selfCentralizing_of_sylow_centralizers T Q hp hne hTM
  intro z _ hz
  exact m23_involutionCentralizer_characteristicTwo ((orderOf_coe z).trans hz)

/-- Condition (E) of the quasithin classification for the concrete M23. -/
theorem m23_evenCharacteristic : IsEvenCharacteristic M23 := by
  intro T M hM hTM
  exact m23_twoLocal_characteristicTwo T M hM.1 hTM

end CFSG.Quasithin.MainConverse
