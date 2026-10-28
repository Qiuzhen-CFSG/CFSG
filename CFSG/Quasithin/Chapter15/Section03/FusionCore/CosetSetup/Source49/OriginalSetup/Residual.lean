module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.Residual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Preamble.Characteristic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic

/-!
# The original extraspecial residual and its normalizer

The Heisenberg alternative of 15.3.7 gives a nontrivial centralizer residual
Y0 = O²(C_Y(V)). Both Y and V are M-invariant, so Y0 is normal in M.
Characteristic two passes to this normal subgroup and forces O₂(Y0) to be
nontrivial. Its characteristic normalizer is two-local; maximality then
identifies N_G(Y0) with the original M.

This is the normalizer used in the actual extraspecial branch of 15.3.49.
Source: Aschbacher--Smith, combined manuscript, 15.3.7 and the proof of
15.3.49(b),(i), printed pp.1122 and 1143--1144.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.OriginalSetup
open ChapterA.Section05To06 ExtraspecialLocal
variable {G : Type*} [Group G] [Finite G]

noncomputable abbrev residual (d : CharacteristicTwo.LocalData G) : Subgroup G :=
  twoResidualAmbient (d.Y ⊓ centralizer (d.V : Set G))

omit [Finite G] in
/-- The actual extraspecial alternative in the quotient convention used by 15.3.49. -/
theorem extraspecialCase (d : CharacteristicTwo.LocalData G)
    (he : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    ExtraspecialCase d.M d.Y d.V := by
  obtain ⟨⟨e⟩,hc,_,ht,_⟩ := he
  exact ⟨(HeisenbergPrime.isExtraspecial (p := 3) (by decide)).of_mulEquiv e.symm,
    (Nat.card_congr e.toEquiv).trans HeisenbergPrime.card,
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide)),
    hc.symm,ht⟩

omit [Finite G] in
theorem residual_le (d : CharacteristicTwo.LocalData G) :
    residual d ≤ d.Y ⊓ centralizer (d.V : Set G) := map_subtype_le _

theorem residual_normalized (d : CharacteristicTwo.LocalData G) :
    d.M ≤ normalizer (residual d : Set G) := by
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hMC : d.M ≤ normalizer (centralizer (d.V : Set G) : Set G) :=
    d.action.normalizes.trans (normalizer_le_normalizer_centralizer _)
  have hn : d.M ≤ normalizer ((d.Y ⊓ centralizer (d.V : Set G) : Subgroup G) : Set G) :=
    (le_inf hMY hMC).trans inf_normalizer_le_normalizer_inf
  change d.M ≤ normalizer (twoResidualAmbient (d.Y ⊓ centralizer (d.V : Set G)) : Set G)
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

theorem residual_ne_bot (d : CharacteristicTwo.LocalData G)
    (he : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    residual d ≠ ⊥ := by
  have h := extraspecialCase d he
  let := h.extraspecial
  change twoResidualAmbient (d.Y ⊓ centralizer (d.V : Set G)) ≠ ⊥
  rw [residual_eq_theta_of_subgroup_exponent_three _ d.Y inf_le_left h.quotient_exponent]
  apply theta_ne_bot_of_three_dvd_card
  rw [h.centralizer_eq]
  exact three_dvd_card_twoCenter _

private theorem normal_coreIn_ne_bot {M K : Subgroup G} (hKM : K ≤ M)
    (hn : (K.subgroupOf M).Normal)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) (hne : K ≠ ⊥) :
    K.pCoreIn 2 ≠ ⊥ := by
  let := hn
  have hK := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hKM)).mp (normal_core_selfCentralizing hc (K.subgroupOf M))
  intro hb
  have hb' : pCore 2 K = ⊥ :=
    ((pCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp hb
  apply hne
  apply (eq_bot_iff_forall K).mpr
  intro x hx
  have hm : (⟨x, hx⟩ : K) ∈ pCore 2 K := hK (by
    intro y hy
    have hy1 : y = 1 := mem_bot.mp (hb' ▸ hy)
    simp only [hy1, one_mul, mul_one])
  have hx1 : (⟨x, hx⟩ : K) = 1 := mem_bot.mp (hb' ▸ hm)
  exact congrArg Subtype.val hx1

/-- The nontrivial centralizer residual has precisely the original maximal local as normalizer. -/
theorem residual_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hM : IsOrderingMaximal d.T d.M)
    (he : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    normalizer (residual d : Set G) = d.M := by
  have hRM : residual d ≤ d.M :=
    (residual_le d).trans (inf_le_left.trans (Chapter14.SourcePreliminaries.sourceResidual_le _ _))
  have hn : ((residual d).subgroupOf d.M).Normal :=
    normal_subgroupOf_of_le_normalizer (residual_normalized d)
  have hcore := normal_coreIn_ne_bot hRM hn
    (hG.evenCharacteristic d.T d.M hM.1.1 d.sylow_le) (residual_ne_bot d he)
  exact normalizer_eq_of_nontrivial_core d.M (residual d) ((residual d).pCoreIn 2)
    hRM hM.1.1 hn hcore le_rfl

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.OriginalSetup
