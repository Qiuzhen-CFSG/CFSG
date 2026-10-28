module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.Source
public import Theory.SpecificGroups.PSL3.CubicComponentAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SelectedCrossingSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal.TerminalAction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.OvergroupAction

/-!
# Excluding the exceptional PSL₃(4) source component

The selected original crossing supplies a nontrivial displaced derived
subgroup inside the two-core, normalized by the original Sylow. The proved
non-enlargement theorem makes the original component a component of its
normalizer. Cubic rank makes it normal there and makes its quotient action
kernel three-prime. This constructs every premise of the terminal E₉ and
Frattini contradiction. The final theorem retains only the original source
setup and the literal PSL₃(4) central-quotient marking.

Source: Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.linear_four_crossing_impossible
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (hne : (⁅((S : Subgroup H).map H.subtype) ⊓ L,
      ((S : Subgroup H).map H.subtype) ⊓ L⁆).conjBy x⁻¹ ≠ ⊥)
    (hcore : (⁅((S : Subgroup H).map H.subtype) ⊓ L,
      ((S : Subgroup H).map H.subtype) ⊓ L⁆).conjBy x⁻¹ ≤ twoCore H)
    (hnorm : (S : Subgroup H).map H.subtype ≤ normalizer
      ((⁅((S : Subgroup H).map H.subtype) ⊓ L,
        ((S : Subgroup H).map H.subtype) ⊓ L⁆).conjBy x⁻¹ : Set G)) : False := by
  let U := (S : Subgroup H).map H.subtype
  let SK := U ⊓ L
  let D := ⁅SK, SK⁆
  let E := D.conjBy x⁻¹
  let NE := normalizer (E : Set G)
  let R := elementaryAbelianMaxJ U
  let N := pairNormalizer D R x⁻¹
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple
    hempty Matrix.PSL3Four.F (by decide : 1 < 2) (by simpa using Matrix.PSL3Four.card_F) e
  have hEC : E ≤ U ⊓ centralizer (L : Set G) := by
    rw [← MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact hcore
  have hLE : IsComponentIn L NE :=
    NonEnlargement.component_in_normalizer_of_binary_rank_two hG localC129Input_knownSimple
      c.T c.maximal c.sylow_le c.unique hempty (MathieuSourceSetup.sourceTuple c)
      ⟨c.component_le, c.component⟩ hgen (by decide : 1 < 2)
      (Or.inl ⟨Matrix.PSL3Four.F, inferInstance, inferInstance,
        by simpa using Matrix.PSL3Four.card_F, ⟨e⟩⟩) hne hEC hnorm
  have hpE : IsPGroup 2 E := (S.isPGroup'.map H.subtype).to_le (hEC.trans inf_le_left)
  have hNErank : primeRank 3 NE ≤ 2 :=
    (hG.twoLocal_sqtk ⟨E, hne, hpE, rfl⟩).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hZ : IsPGroup 2 (center L) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG localC129Input_knownSimple hempty]
    exact pCore_isPGroup
  have hZcop : Nat.Coprime 3 (Nat.card (center L)) := by
    obtain ⟨m, hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hLrank : 2 ≤ primeRank 3 L :=
    Matrix.PSL3.CubicComponentAction.component_rank hZ
      (by simpa using Matrix.PSL3Four.card_F) (by decide : Even 2) e
  let eL : L.subgroupOf NE ≃* L := subgroupOfEquivOfLe hLE.1
  have hZlocal : Nat.Coprime 3 (Nat.card (center (L.subgroupOf NE))) := by
    rw [Nat.card_congr (centerCongr eL).toEquiv]
    exact hZcop
  have hLlocal : 2 ≤ primeRank 3 (L.subgroupOf NE) := by
    rw [primeRank_congr 3 eL]
    exact hLrank
  let : (L.subgroupOf NE).Normal := hLE.2.normal_of_coprime_center_primeRank
    3 hZlocal (by omega)
  have hNL : N ≤ normalizer (L : Set G) :=
    (show N ≤ NE from inf_le_left.trans inf_le_right).trans
      ((normal_subgroupOf_iff_le_normalizer hLE.1).mp inferInstance)
  obtain ⟨P, hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  have hPambient : (P : Subgroup L).map L.subtype = SK := by
    rw [hP, subgroupOf_map_subtype]
  have hRU : R ≤ U := sSup_le fun _ h => h.1
  have hSKR : SK ≤ R := by
    have hprod : R = SK ⊔ (R ⊓ centralizer (L : Set G)) :=
      MathieuSourceSetup.ambient_thompson_product c hgen
      (MathieuSourceSetup.linear_four_thompson_product c hG localC129Input_knownSimple
        hempty hgen e)
    rw [hprod]
    exact le_sup_left
  have hSK : SK = R ⊓ L :=
    le_antisymm (le_inf hSKR inf_le_right) (le_inf (inf_le_left.trans hRU) inf_le_right)
  have hNP : N ≤ normalizer ((P : Subgroup L).map L.subtype : Set G) := by
    rw [hPambient, hSK]
    exact (le_inf inf_le_right hNL).trans inf_normalizer_le_normalizer_inf
  let : IsQuasisimple L := (show IsComponentIn L H from ⟨c.component_le, c.component⟩).quasisimple
  obtain ⟨α, hα, hαP, hαker⟩ := component_sylow_quotient_action_in_overgroup
    L N NE e P hLE.1 (inf_le_left.trans inf_le_right) hNL hNP hZcop hLrank hNErank
  exact MathieuSourceSetup.linear_four_terminal_of_component_action c hG hempty hgen e
    x hxT hxS hxN hx2 (hEC.trans inf_le_right) P hPambient hNL α hα hαP hαker

theorem MathieuSourceSetup.linear_four_impossible
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL) : False := by
  obtain ⟨x, hxT, hxS, hxN, hx2, hne, hcore, hnorm⟩ :=
    MathieuSourceSetup.linear_four_selected_crossing_derived_core c hG hempty hgen e
  exact MathieuSourceSetup.linear_four_crossing_impossible c hG hempty hgen e
    x hxT hxS hxN hx2 hne (hcore.trans inf_le_right) hnorm

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
