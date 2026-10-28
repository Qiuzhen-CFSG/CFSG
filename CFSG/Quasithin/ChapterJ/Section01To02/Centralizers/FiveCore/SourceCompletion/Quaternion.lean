module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.FixedSections
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Local
public import Theory.GroupTheory.QuaternionElementarySupplementRecognition

/-!
# The source quaternion five-centralizer

The actual C_Q(B₅) has order eight and meets U in Z. The earlier source
cubic quaternion gives HC = C_Q(B)U, a central product with elementary U.
Quaternion recognition therefore identifies C_Q(B₅) with Q₈. The existing
centralizer promotion theorem constructs its actual Sylow position in
C_G(B₅), the order-forty local product, and all fixed-section fields.
No quaternion witness or fixed-space equation remains a premise.

Source: Aschbacher–Smith J.2.7(5), printed p.435, using J.2.3(7).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

/-- The literal centralizer of the chosen five-subgroup is quaternion. -/
theorem five_centralizer_quaternion (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nonempty (CQ B5 ≃* QuaternionGroup 2) := by
  let cp := Fusion.centralProductData_of_quaternion d c.sylowThree
    (SourceCompletion.quaternion c.sylowThree)
  have hBU : Nat.card (Fusion.HB d.toTypeRuSetup c.sylowThree ⊓ d.toTypeRuSetup.U : Subgroup G) = 2 := by
    rw [cp.intersection_eq,d.card_Z]
  have hBHC : Fusion.HB d.toTypeRuSetup c.sylowThree ≤ d.toTypeRuSetup.HC := by
    rw [cp.product_eq]
    exact le_sup_left
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  apply quaternion_of_eight_in_quaternion_elementary_product
    (Fusion.HB d.toTypeRuSetup c.sylowThree) d.toTypeRuSetup.U (CQ B5)
    cp.quaternion hBU (hBHC.trans inf_le_right)
  · rw [← cp.product_eq]
    exact five_centralizer_le_HC B5
  · exact five_centralizer_card B5
  · rw [five_centralizer_inf_U,d.card_Z]

/-- All local quaternion and Sylow fields in the original five-centralizer. -/
theorem fiveQuaternionData_source (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nonempty (FiveQuaternionData B5) :=
  c.fiveQuaternionData_of_local_quaternion d.card_Z B5
    (five_centralizer_quaternion c B5) (five_centralizer_le_HC B5) (five_centralizer_inf_U B5)

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
