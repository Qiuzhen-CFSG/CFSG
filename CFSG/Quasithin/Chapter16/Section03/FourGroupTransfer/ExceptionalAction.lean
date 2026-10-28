module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ComponentRestriction
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.Reduction
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HigmanSims

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.AutomorphismBound

/-!
# The exceptional-action reduction for 16.3.5

The checked deductions normalize the actual layer closure, transport the
16.3.4 exclusion through Sylow conjugacy, prove its two-core nontrivial, and
exclude incompatible A₈/A₆ centralizer layers. Faithfulness and order four
identify the ambient action with the full automorphism centralizer once its
intrinsic E₄ model is supplied. Elementary abelianness is derived here.
The A₅/Sz(8) automorphism two-part bound is proved on the concrete models.

`exceptional_of_calculation` is a conditional assembly result. The swapped
branch, the intrinsic automorphism-centralizer calculation, and the existence
of the two HS witnesses remain required for the source alternative. They are
not asserted by this module or by the definitions in `Inputs`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.5–6, printed pp.1178–1179 / PDF pp.1195–1196.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
open Subgroup Theory.GroupTheory ClassificationModels
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- Commuting ambient subgroups induce commuting automorphisms. -/
theorem action_range_le_centralizer {E L I : Subgroup G}
    (hLI : L ≤ I) (hn : E ≤ normalizer (I : Set G))
    (hc : E ≤ centralizer (L : Set G)) :
    (inducedAction E I hn).range ≤
      centralizer ((inducedAction L I (hLI.trans I.le_normalizer)).range : Set (MulAut I)) := by
  rintro _ ⟨a, rfl⟩ b ⟨l, rfl⟩
  change I.normalizerMonoidHom (Subgroup.inclusion (hLI.trans I.le_normalizer) l) *
      I.normalizerMonoidHom (Subgroup.inclusion hn a) =
    I.normalizerMonoidHom (Subgroup.inclusion hn a) *
      I.normalizerMonoidHom (Subgroup.inclusion (hLI.trans I.le_normalizer) l)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hc a.property) l l.property

/-- Transport the elementary structure along the actual four-group model. -/
theorem elementary_of_four_model {A : Type*} [Group A]
    (e : A ≃* (Fin 2 → Multiplicative (ZMod 2))) : IsElementaryAbelian 2 A := by
  refine { toIsMulCommutative := IsMulCommutative.of_comm ?_, exponent_dvd_p := ?_ }
  · intro a b
    apply e.injective
    simp only [map_mul, mul_comm]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply e.injective
    rw [map_pow, map_one]
    ext j
    exact (show ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 by decide) (e a j)

/-- A faithful group of order four in a full automorphism centralizer
is that centralizer when the latter has the actual E4 model. -/
theorem full_action_of_centralizer_model [Finite G] {E L I : Subgroup G}
    (hLI : L ≤ I) (hn : E ≤ normalizer (I : Set G))
    (hc : E ≤ centralizer (L : Set G)) (hcard : Nat.card E = 4)
    (hfaith : Function.Injective (inducedAction E I hn))
    (hmodel : Nonempty
      (centralizer ((inducedAction L I (hLI.trans I.le_normalizer)).range : Set (MulAut I)) ≃*
        (Fin 2 → Multiplicative (ZMod 2)))) :
    IsElementaryAbelian 2 E ∧ Nonempty (E ≃* (Fin 2 → Multiplicative (ZMod 2))) ∧
      (inducedAction E I hn).range =
        centralizer ((inducedAction L I (hLI.trans I.le_normalizer)).range : Set (MulAut I)) := by
  obtain ⟨eC⟩ := hmodel
  let C := centralizer ((inducedAction L I (hLI.trans I.le_normalizer)).range : Set (MulAut I))
  have hle := action_range_le_centralizer hLI hn hc
  let f : E →* C := (inducedAction E I hn).codRestrict C
    (fun a => hle ⟨a, rfl⟩)
  have hinj : Function.Injective f := fun a b hab => hfaith (congrArg Subtype.val hab)
  have hC : Nat.card C = 4 := by
    rw [Nat.card_congr eC.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard.trans hC.symm⟩
  let eE := (MulEquiv.ofBijective f hbij).trans eC
  refine ⟨elementary_of_four_model eE, ⟨eE⟩, le_antisymm hle ?_⟩
  intro a ha
  obtain ⟨x, hx⟩ := hbij.surjective ⟨a, ha⟩
  exact ⟨x, congrArg Subtype.val hx⟩

/-- Once the intrinsic action calculation and HS witnesses are supplied,
the full published exceptional contract follows. The nontrivial core uses
16.3.4 only after constructing its exact setup by Sylow conjugacy. -/
theorem exceptional_of_calculation [Finite G]
    {T : Sylow 2 G} {z : G} {E L I : Subgroup G} {t i : G}
    (h : CentralComponentSetup T z L)
    (hnL : (L.subgroupOf (involutionCentralizer z)).Normal)
    (exclude : ∀ (J : Subgroup G) (a b : G),
      ExclusionSetup T z L J a b → ¬ IsExcludedSimple J)
    (hs : ComponentTransfer.Setup t i L)
    (hcard : Nat.card E = 4) (hc : CentralizesAsComponent E L)
    (hEL : E ≤ centralizer (L : Set G))
    (hIeq : I = ComponentTransfer.layerClosure (involutionCentralizer i) L)
    (hI : IsCentralizerComponent i I) (hproper : L < I)
    (hcomm : ⁅I, zpowers t⁆ = I)
    (hn : E ≤ normalizer (I : Set G))
    (calculation : ActionCalculation L I hproper.le)
    (hsWitness : Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.hs.Carrier) →
      pCore 2 I ≠ ⊥ → MixedHSLayers E I) : ExceptionalEnlargement E L i := by
  have hLI : Theory.GroupTheory.IsComponentIn L (I ⊓ involutionCentralizer t) :=
    Theory.GroupTheory.IsComponentIn.restrict hs.component
      (le_inf hproper.le hs.component.1) inf_le_right
  have hmodel : IsExcludedSimple (I ⧸ pCore 2 I) := by
    rcases calculation.models with hm | hhs
    · rcases hm with ⟨_, hm | hj⟩ | ⟨_, hr⟩
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr (Or.inl hj))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hr)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hhs)))
  have hcore := twoCore_ne_bot_of_exclusion h hnL exclude hs hI hLI hcomm hmodel
  have hnotHS : ¬ Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.hs.Carrier) := by
    intro hhs
    obtain ⟨s, t, hsE, hs1, htE, ht1, h8, h6⟩ := hsWitness hhs hcore
    exact not_components_of_alternating_layers hproper.le hc hsE hs1 htE ht1 h8 h6
  have hmodels := calculation.models.resolve_right hnotHS
  let := hI.quasisimple
  have hfaith := faithful_inducedAction_of_components E L I hproper hn hc
  obtain ⟨helem, hfour, himage⟩ := full_action_of_centralizer_model hproper.le hn hEL
    hcard hfaith calculation.centralizer_model
  subst I
  exact ⟨hproper, hI, hn, hfaith, helem, hfour,
    himage, hcore, hmodels⟩

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
