module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Power
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.PlusType

/-!
# Discharging the power-form fields of the source recognition input

The earlier extraspecial theorem constructs the same quadratic form used by
both action recognition and the plus-type conclusion. Only the independent
marked actor conclusions of 15.3.56(4–6) remain as geometric inputs here.

Source: Aschbacher–Smith, 15.3.55–56 and 15.3.58(2), pp.1147–1149.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition Recognition.NormalReduction
variable {G : Type*} [Group G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass} {v : ActorQuotient Z} {s : ℕ}

/-- The literal recognition consumer, with all orthogonal and square-map
premises discharged by source 15.3.55. -/
theorem action_power_inputs (d : EarlierSourceInputs Z ZS V M C v s)
    (X : Subgroup G) (hXT : X ≤ (d.T : Subgroup G))
    (hVX : actorImage Z V ≤ actorImage Z X)
    (helem : IsElementaryAbelian 2 (actorImage Z X))
    (hcard : Nat.card (actorImage Z X) = 2 ^ (s + 1))
    (hextra : IsExtraspecial 2 (closureU Z ZS))
    (hcenter : center (closureU Z ZS) = Z.subgroupOf (closureU Z ZS)) :
    ∃ a : EarlierActionInputs d, a.X = X ∧ EarlierPowerInputs d a := by
  let := hextra
  obtain ⟨q, hn, hi, hp, _⟩ := exists_actor_power_form Z ZS hcenter d.kernel
  let a : EarlierActionInputs d := {
    X := X
    X_le_T := hXT
    Vstar_le_Xstar := hVX
    elementary := helem
    card_actor := hcard
    quadratic := q
    nondegenerate := hn
    invariant := hi }
  exact ⟨a, rfl, ⟨hextra, hcenter, hp⟩⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
