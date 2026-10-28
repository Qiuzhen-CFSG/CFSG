module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramAmbientCoreSelection
/-!
# Characteristic two for the selected Sylow supplement

A subgroup between O₂(H) and H has self-centralizing two-core when H
does. Applying this to the selected residual joined with S proves the
characteristic-two clause needed for the first F.1.1 parabolic.

Source: Aschbacher--Smith 14.2.15 and F.1.1(f), printed pp.985 and 259.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
variable {G : Type*} [Group G] [Finite G]

theorem selected_join_generalizedFitting_eq_twoCore
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hH : H ∈ Chapter1.He G) (hcore : H.pCoreIn 2 ≤ S) :
    generalizedFitting (L ⊔ S : Subgroup G) = pCore 2 (L ⊔ S : Subgroup G) := by
  let X := L ⊔ S
  have hXH : X ≤ H := sup_le hLH hSH
  have hQ : H.pCoreIn 2 ≤ X.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hcore.trans le_sup_right)
      (hXH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply Chapter1.mem_He_iff.mp
  exact (inf_le_inf hXH (centralizer_le hQ)).trans (hH.trans hQ)

theorem source_selected_join_generalizedFitting_eq_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (H L S : Subgroup G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hLH : L ≤ H) (hST : S ≤ (T : Subgroup G))
    (hcore : H.pCoreIn 2 ≤ S) :
    generalizedFitting (L ⊔ S : Subgroup G) = pCore 2 (L ⊔ S : Subgroup G) :=
  selected_join_generalizedFitting_eq_twoCore H L S hLH (hST.trans hH.2)
    (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH) hcore
end CFSG.Quasithin.Chapter14.Section02
