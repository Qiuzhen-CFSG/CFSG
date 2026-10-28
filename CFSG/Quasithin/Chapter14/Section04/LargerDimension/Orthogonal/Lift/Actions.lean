module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.FixedPoints
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.MovedInterval
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.Transvections

/-!
# Action calculations for the orthogonal lift

The selected binary A₅ action on the literal moved image constructs the
elementary lift D and its base A. Commutator duality identifies U/A with
all central functionals A/⟨z⟩ → ⟨z⟩, whose automorphisms a ↦ a f(a⟨z⟩)
are exactly the conjugations induced by U. Displacement independently
identifies U/A with the selected binary module. The chief series
1 < ⟨z⟩ < A < D retains its actual quotient actions and relative normality.

The assembly also proves C_D(u)≤A for u∈U\A and reuses the established
centralizer identities. Its only module input is the selected moved-image
identification; irreducibility, the lifted modules and the full transvection
action are conclusions. The orthogonal-selection owner supplies that input,
and the parent Lift module retains the other branches of the source proof.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- The source centralizer bound, constructing the elementary lift from its
irreducible moved image before applying the three-subgroups calculation. -/
theorem centralizerLift_element_centralizer_le_base_of_moved_image
    (U K : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U) (hKU : K ≤ normalizer (U : Set G))
    (hKi : K ≤ centralizer ({i} : Set G))
    (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (ρ : K →* MulAut (U ⧸ center U))
    (hρ : ∀ k : K, ∀ u : U, ρ k (QuotientGroup.mk' (center U) u) =
      QuotientGroup.mk' (center U) ⟨(k : G) * (u : G) * (k : G)⁻¹,
        (mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩)
    (hirr : ∀ F : Subgroup (U ⧸ center U),
      F ≤ ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U)) →
      (∀ k : K, ∀ v ∈ F, ρ k v ∈ F) → F = ⊥ ∨
        F = ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U)))
    (u : G) (hu : u ∈ U) (huA : u ∉ liftBase U z i) :
    centralizerLift U z i ⊓ centralizer ({u} : Set G) ≤ liftBase U z i := by
  obtain ⟨hD, _, hA, hAcard⟩ := centralizerLift_elementary_and_card_of_moved_image
    U K z i hz hi hZ hiU hiz hout hKU hKi hmoved ρ hρ hirr
  exact centralizerLift_element_centralizer_le_base U z i hi hZ hiU hiz hUcard
    hD hA hAcard u hu huA

/-- The constructed lift actions, including the original commutator formula.
This is output data: `MovedCoreModel.lift_actions` constructs every field from
the selected moved module, without assuming any of these action conclusions. -/
structure LiftActionResult (U K : Subgroup G) (z i : G)
    (hKU : K ≤ normalizer (U : Set G)) (m : MovedCoreModel U K i hKU) where
  chief : ChiefModuleResult U K z i hKU m
  base_eq_commutator : liftBase U z i = ⁅U, zpowers i⁆
  element_centralizer : ∀ u ∈ U, u ∉ liftBase U z i →
    centralizerLift U z i ⊓ centralizer ({u} : Set G) ≤ liftBase U z i
  base_self_centralizer : U ⊓ centralizer (liftBase U z i : Set G) = liftBase U z i
  fixed_line : centralizerLift U z i ⊓ centralizer (U : Set G) = zpowers z
  self_centralizer :
    (U ⊔ centralizerLift U z i) ⊓ centralizer (centralizerLift U z i : Set G) =
      centralizerLift U z i
  elementary_Z : IsElementaryAbelian 2 (zpowers z)
  functionalConfiguration :
    ExtraspecialCentralFunctionals.Configuration U (liftBase U z i) (zpowers z)
  duality : let _ := chief.elementary_A
    let _ := elementary_Z
    let _ := chief.normal_AU
    (U ⧸ (liftBase U z i).subgroupOf U) ≃*
      ((liftBase U z i ⧸ (zpowers z).subgroupOf (liftBase U z i)) →* zpowers z)
  duality_formula : let _ := chief.elementary_A
    let _ := elementary_Z
    let _ := chief.normal_AU
    ∀ (u : U) (a : liftBase U z i),
      (duality (QuotientGroup.mk' ((liftBase U z i).subgroupOf U) u)
        (QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i)) a) : G) =
          ⁅(u : G), (a : G)⁆
  full_transvections : let _ := chief.elementary_A
    let _ := elementary_Z
    let c := functionalConfiguration
    (ExtraspecialCentralFunctionals.pairing c).ker = (liftBase U z i).subgroupOf U ∧
      Function.Surjective (ExtraspecialCentralFunctionals.pairing c) ∧
      Function.Injective (ExtraspecialCentralFunctionals.twists c.center_le) ∧
      ExtraspecialCentralFunctionals.conjugation c =
        (ExtraspecialCentralFunctionals.twists c.center_le).comp
          (ExtraspecialCentralFunctionals.pairing c) ∧
      (ExtraspecialCentralFunctionals.conjugation c).range =
        (ExtraspecialCentralFunctionals.twists c.center_le).range

namespace MovedCoreModel
variable {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
variable [IsExtraspecial 2 U] (m : MovedCoreModel U K i hKU)

/-- Construct all the lift action calculations from the actual selected binary
module. The interval premise of the elementary-lift theorem is discharged by
`chief_modules`, using irreducibility of that binary module. -/
theorem lift_actions (z : G) (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U) (hKi : K ≤ centralizer ({i} : Set G))
    (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (movedImage U i) = 16) :
    Nonempty (LiftActionResult U K z i hKU m) := by
  obtain ⟨r⟩ := m.chief_modules z hz hi hZ hiU hiz hout hKi hUcard hmoved
  let _ := r.elementary_A
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  let hZE := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  let _ := hZE
  let c := liftBase_centralFunctionalConfiguration U z i hz hZ hiU hUcard
    r.elementary_A r.card_A
  refine ⟨{
    chief := r
    base_eq_commutator := (liftBase_eq_commutator_and_card U z i hZ hiU hmoved).1
    element_centralizer := centralizerLift_element_centralizer_le_base U z i hi
      hZ hiU hiz hUcard r.elementary_D r.elementary_A r.card_A
    base_self_centralizer := c.self_centralizing
    fixed_line := centralizerLift_fixed_line U z i hz hi hZ hiU r.elementary_D r.card_A
    self_centralizer := centralizerLift_self_centralizer U z i hZ hiU hUcard
      r.elementary_D r.elementary_A r.card_A
    elementary_Z := hZE
    functionalConfiguration := c
    duality := ExtraspecialCentralFunctionals.quotientEquiv c
    duality_formula := ExtraspecialCentralFunctionals.quotientEquiv_apply c
    full_transvections := ?_ }⟩
  exact ⟨ExtraspecialCentralFunctionals.pairing_ker c,
    ExtraspecialCentralFunctionals.pairing_surjective c,
    ExtraspecialCentralFunctionals.twists_injective c.center_le,
    ExtraspecialCentralFunctionals.conjugation_eq_twists_pairing c,
    ExtraspecialCentralFunctionals.conjugation_range c⟩
end MovedCoreModel

/-- The action part of Lemma 14.4.9 for the literal source residual
K₀ = O²(C_{C_G(z)}(i)). Its centralization of i follows from its definition;
the selection input is exactly the moved binary A₅ module. -/
theorem diagonalResidual_lift_actions
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) i ≤ normalizer (U : Set G))
    (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (movedImage U i) = 16)
    (m : MovedCoreModel U (diagonalResidual (centralizer ({z} : Set G)) i) i hKU) :
    Nonempty (LiftActionResult U (diagonalResidual (centralizer ({z} : Set G)) i) z i hKU m) := by
  have hKi : diagonalResidual (centralizer ({z} : Set G)) i ≤ centralizer ({i} : Set G) :=
    (map_subtype_le _).trans inf_le_right
  exact m.lift_actions z hz hi hZ hiU hiz hout hKi hUcard hmoved

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
