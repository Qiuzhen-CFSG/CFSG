module

public import CFSG.Quasithin.MainConverse.SuzukiRank
public import CFSG.Quasithin.MainConverse.SuzukiSections
public import CFSG.Quasithin.MainConverse.SuzukiEven

/-!
# The Suzuki branch of the converse

The QT and E clauses and every simple-section identification have been proved
for the concrete Suzuki family. The only remaining parameter here is inclusion
of the constructed known-simple catalogue in K. Final Main Theorem assembly
must instantiate K with the complete catalogue and prove that inclusion.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed p.4, and the repeated
Main Theorem on p.482. The parameter m ≥ 1 means q = 2^(2m+1) ≥ 8.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple BenderSuzuki.MatrixGroups

public theorem suzuki_isQTKE_of_catalogue {G : Type*} [Group G] [Finite G]
    {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* SuzukiMatrixGroup m) : IsQTKE K G :=
  ⟨suzuki_quasithin_of_iso hm e, suzuki_properK_of_catalogue hK hm e,
    suzuki_evenCharacteristic_of_iso hm e⟩

end CFSG.Quasithin.MainConverse
