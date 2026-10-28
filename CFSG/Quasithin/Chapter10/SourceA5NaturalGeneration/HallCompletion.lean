module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.SelectionAssembly
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.HallAssembly
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.CartanAxis
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.RankLowerOriginal
/-!
# Natural A5 generation after the actual Hall placement

The actual odd Hall subgroup in the original orbit Borel lies in an elementary
order-nine torus. Its nontrivial faithful omega action removes both fixed
centers. The source classifier then selects a paired field-four component,
forces nine to divide this same Hall subgroup, and recovers both natural
blocks with a compatible Hall cubic. Thus the Hall is the full torus.
The nonzero alpha fixed subgroup identifies its cubic with a literal original
axis. The resulting oriented pair contradicts the terminal component's cubic
rank bounds.

This discharges every intermediate source, component, block, axis and rank
premise. The remaining earlier input is the actual Hall placement in the
original Borel. Source: Aschbacher--Smith 10.2.3(4), printed pp.745--747.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterC ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance hallCompletionOriginalMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable {F : Type*} [Field F] [CharP F 2]
local instance hallCompletionFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Original natural-four source 10.2.3(4), with its earlier Hall placement explicit. -/
theorem source_natural_generation_le_one_of_hall_borel
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) : generationParameter H ≤ 1 := by
  by_contra hsmall
  have hlarge : 1 < generationParameter H := lt_of_not_ge hsmall
  have hBR : B.map H.subtype ≤ localOrbit T L :=
    hBB.trans ((map_subtype_le _).trans inf_le_left)
  have hBodd : Odd (Nat.card B) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact even_iff_two_dvd.mp he
  have hB3 : IsPGroup 3 (B.map H.subtype) := source_a5_hstar_odd_subgroup_isThreeGroup
    D e hn hH (B.map H.subtype) (map_subtype_le B) (hBR.trans le_sup_left)
    (by simpa only [card_map_of_injective H.subtype_injective] using hBodd)
  obtain ⟨C,hBC,hCB,_,hCc,hCe⟩ := source_a5_exists_hall_torus_of_borel_placement
    D e hn (B.map H.subtype) hB3 hBB
  let := hCe
  let : IsElementaryAbelian 3 (B.map H.subtype) := IsElementaryAbelian.of_injective
    (inclusion hBC) (inclusion_injective hBC)
  obtain ⟨hZH,hCZ,hzL,hzH⟩ := source_natural_fixed_centers_of_hall D e hn ht htn hcross
    hF f n hi hH hlarge B hBM hHall hBR
  obtain ⟨h9,K,P,pair⟩ := source_natural_hall_pair_of_three_hall D e hn hH hZH hF f n
    hzL hzH B hBM hHall
    (hB3.of_equiv (B.equivMapOfInjective H.subtype H.subtype_injective).symm) hlarge hCZ
  have hBc : Nat.card (B.map H.subtype)=9 := by
    apply Nat.dvd_antisymm
    · exact hCc ▸ card_dvd_of_le hBC
    · simpa only [card_map_of_injective H.subtype_injective] using h9
  have haxis := source_original_cartan_axis_of_alpha_fixed D e hn hH hZH hF f n ht htn
    hzL (B.map H.subtype) P hBB hBc inferInstance pair.cubic_hall pair.cubic_card pair.alpha_fixed
  obtain ⟨s,O⟩ := source_original_orient_selected_axis D e hn ht htn pair.original_block hzL
    K (B.map H.subtype) P pair.selected_natural pair.selected_core pair.selected_center
    pair.selected_sylow pair.baumann_normalizes_selected pair.escapes hBB hBc
    pair.cubic_block pair.cubic_card pair.hall_normalizes haxis
  exact O.false pair.original_block hzL pair.original_natural pair.original_core
    pair.baumann_le_orbit pair.baumann_sylow pair.baumann_normalizes_original
end CFSG.Quasithin.Chapter10
