module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceOddNormalizerComplete

/-!+# The literal Hall placement and the original A₅ weak-closure endpoint

The full-Hall kernel argument uses the proved 4.4.13(1) escape and the
proved nonnormal-pair case of 4.4.3 on the same odd actor. Its faithful Hall
image lies in L₀ by the actual A₅ × A₅ quotient action and the cubic and
five residual identities. We retain that very Hall subgroup of H ∩ M.

The separated minimal setup therefore supplies the literal placement used
by the weak-closure endgame. No component, inner-action, odd-normalizer or
Hall-placement premise remains. Minimality, the full cubic bound, seed
separation and point control are the earlier source inputs of this interface.

Source: Aschbacher--Smith 4.4.3, 4.4.13(1), 10.2.3(1--2) and
10.2.12--13, printed pp.619--624,744--745,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual full Hall witness is faithful and lies in L₀ itself.
Both conclusions concern its unchanged image through the subtype H → G. -/
theorem source_a5_hstar_hall_placement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
      B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ ∧
      B.map H.subtype ≤ localOrbit T L := by
  obtain ⟨B,hBM,hHall,hfaith⟩ :=
    source_a5_hstar_hall_faithful D e hn ht htn hcoords hH hlarge
  have hodd : Odd (Nat.card (B.map H.subtype)) := by
    rw [card_map_of_injective H.subtype_injective]
    apply Nat.not_even_iff_odd.mp
    intro he
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact even_iff_two_dvd.mp he
  exact ⟨B,hBM,hHall,hfaith,
    source_a5_faithful_odd_subgroup_le_orbit D e hn (B.map H.subtype)
      (map_le_iff_le_comap.mpr hBM) hodd hfaith⟩

/-- The source n(H)>1 branch has n(H)=2 and its literal placed Hall
subgroup, with the separated coordinates constructed on the chosen setup. -/
theorem source_a5_hstar_generation_eq_two_and_hall_placement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    generationParameter H = 2 ∧
      ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
        IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
        B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ ∧
        B.map H.subtype ≤ localOrbit T L := by
  obtain ⟨B,hBM,hHall,hfaith,hBL⟩ := source_a5_hstar_hall_placement
    D e hn ht htn
    (source_a5_original_bounded_separated_coordinates D e hn ht htn hD hbound hsep)
    hH hlarge
  have hupper := source_a5_hstar_generation_bound_of_hall_placement
    D e hn hH B hBM hHall (hBL.trans le_sup_left)
  exact ⟨by omega,B,hBM,hHall,hfaith,hBL⟩

local instance sourcePlacementMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance sourcePlacementFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- Original 10.2.12--13 with the Hall placement discharged. The natural
marking uses the literal quotient L/O₂(L) and the original moved module. -/
theorem source_a5_natural_and_parameters_eq_two
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    globalW D.fullModule (T : Subgroup G) = 2 ∧ generationParameter H = 2 ∧
      ∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  obtain ⟨hi,hcross⟩ := source_a5_original_irreducible_of_minimal_separated_seed
    D e hn ht htn hD hbound hsep
  have hb := source_a5_hstar_generation_bound D e hn ht htn hD hbound hsep hH
  have hlargeE : (1 : ℕ∞) < (generationParameter H : ℕ∞) :=
    (source_a5_globalW_gt_one D e hi hn ht htn hcross hcent).trans_le
      (source_a5_hstar_globalW_le_generation D e hcent hH hb)
  have hlarge : 1 < generationParameter H := by exact_mod_cast hlargeE
  obtain ⟨_,B,hBM,hHall,_,hBL⟩ :=
    source_a5_hstar_generation_eq_two_and_hall_placement
      D e hn ht htn hD hbound hsep hH hlarge
  exact source_a5_natural_and_parameters_eq_two_of_hall_placement
    D e hi hn ht htn hcross hcent hH B hBM hHall (hBL.trans le_sup_left)

end CFSG.Quasithin.Chapter10
