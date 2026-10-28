module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Faithful
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureEndgame
/-!
# Actual Hall faithfulness in the original A₅ consumers

The faithful odd Hall action places the literal ambient image in L₀ and
therefore in L₀T. Applying the original generation and weak-closure theorems
removes their Hall-placement premise. The section kernel's triviality is the
remaining input supplied by the separate odd-normalizer argument.
Source: Aschbacher–Smith 10.2.3 and 10.2.12–13, pp.745,754–755.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem hall_image_odd {H : Subgroup G} (B : Subgroup H)
    (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    Odd (Nat.card (B.map H.subtype)) := by
  rw [card_map_of_injective H.subtype_injective]
  apply Nat.not_even_iff_odd.mp
  intro he
  apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
  rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
  exact even_iff_two_dvd.mp he

/-- The original faithful Hall image gives the source generation upper bound. -/
theorem source_a5_hstar_generation_bound_of_hall_faithful
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hfaith : B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥) :
    generationParameter H ≤ 2 := by
  have hB := source_a5_faithful_odd_subgroup_le_orbit D e hn (B.map H.subtype)
    (map_le_iff_le_comap.mpr hBM) (hall_image_odd D B hBM hHall) hfaith
  exact source_a5_hstar_generation_bound_of_hall_placement D e hn hH B hBM hHall
    (hB.trans le_sup_left)

local instance faithfulConsumersMovedElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

local instance faithfulConsumersFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The literal original faithful Hall subgroup feeds the weak-closure endgame. -/
theorem source_a5_natural_and_parameters_eq_two_of_hall_faithful
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hfaith : B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥) :
    globalW D.fullModule (T : Subgroup G) = 2 ∧ generationParameter H = 2 ∧
      ∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  have hB := source_a5_faithful_odd_subgroup_le_orbit D e hn (B.map H.subtype)
    (map_le_iff_le_comap.mpr hBM) (hall_image_odd D B hBM hHall) hfaith
  exact source_a5_natural_and_parameters_eq_two_of_hall_placement
    D e hi hn ht htn hcross hcent hH B hBM hHall (hB.trans le_sup_left)
end CFSG.Quasithin.Chapter10
