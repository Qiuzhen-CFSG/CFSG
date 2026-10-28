module
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core.Center
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.LocalA5Placement

/-!
# The Ru local A₅ radical has small center

The full-Sylow local placement puts a source-sized local subgroup in the
actual max6 carrier with the same two-core. Transporting the marked center
calculation therefore bounds its two-core center by two. This is the concrete
model input for excluding the Ru smaller-group row in Aschbacher–Smith
A.3.14 and 10.2.9, printed pp.48–49 and 750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
open Rudvalis Rudvalis.SylowOvergroups

/-- Every genuine local subgroup in the Ru A₅ row has small two-core center. -/
theorem local_a5_core_center_card_le_two (P : Sylow 2 Model) (B : Subgroup Model)
    (hB : (B.subgroupOf (B ⊔ (P : Subgroup Model))).IsSubnormal)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hcore : Nat.card (pCore 2 B) = 2048) :
    Nat.card (center (pCore 2 B)) ≤ 2 := by
  obtain ⟨f⟩ := local_a5_core_equiv P B hB e hcore
  rw [Nat.card_congr (centerCongr f).toEquiv]
  exact Max6Core.max6_core_center_card_le_two

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
