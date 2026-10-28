module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.PairTransport
public import Theory.Representation.NaturalCommutantOrder

/-!
# Hall-kernel fixation in the two marked non-A₅ natural rows

The model map factors through the original L/O₂(L), and the coordinate
isomorphism intertwines its action on the literal first moved quotient.
The scalar-commutant bounds and actual Sylow conjugation then fix the Hall
kernel on the whole original module. No second row marking is required.

These are conditional row applications. Constructing the first natural
marking from the FF hypothesis remains necessary for source assembly; no
arbitrary full-module irreducibility or multiplicity-one assertion is made.
The non-FF generation/reselection and zero-two-core normalizer branches also
remain separate obligations.
Source: Aschbacher--Smith, 10.1.1(1),(3) and 10.2.3(2), pp.741,745.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The model homomorphism is obtained from the original component quotient. -/
noncomputable def sourceMovedModelHom {J : Type*} [Group J]
    (a : (L ⧸ pCore 2 L) ≃* J) : L.subgroupOf D.maximalLocal →* J :=
  a.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp
    (subgroupOfEquivOfLe ((le_componentOrbit L T).trans
      (localOrbit T L).le_normalizer)).toMonoidHom)

/-- The model map retains the original component element and two-core projection. -/
theorem sourceMovedModelHom_apply {J : Type*} [Group J]
    (a : (L ⧸ pCore 2 L) ≃* J) (k : L.subgroupOf D.maximalLocal) :
    sourceMovedModelHom D a k = a (QuotientGroup.mk' (pCore 2 L) ⟨k.val.val,k.property⟩) := by rfl

/-- The component-model map is surjective through the literal two-core quotient. -/
theorem sourceMovedModelHom_surjective {J : Type*} [Group J]
    (a : (L ⧸ pCore 2 L) ≃* J) : Function.Surjective (sourceMovedModelHom D a) :=
  a.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (subgroupOfEquivOfLe ((le_componentOrbit L T).trans
      (localOrbit T L).le_normalizer)).surjective)

/-- The first moved quotient in the single natural SL₂ row has the required prime support. -/
theorem source_natural_sl2_moved_commutant_dvd {F : Type*} [Field F] [Finite F]
    (a : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (e : sourceMovedQuotient D L ≃* Multiplicative (Fin 2 → F))
    (he : ∀ k v, (e (sourceMovedQuotientAction D L L L.le_normalizer k v)).toAdd =
      (sourceMovedModelHom D a k).val.mulVec (e v).toAdd) :
    Nat.card (centralizer ((sourceMovedQuotientAction D L L L.le_normalizer).range :
      Set (MulAut (sourceMovedQuotient D L)))) ∣ Nat.card (L ⧸ pCore 2 L) := by
  rw [Nat.card_congr a.toEquiv]
  exact sl2_natural_commutant_card_dvd _ (sourceMovedModelHom D a) (sourceMovedModelHom_surjective D a) e he

/-- The first moved quotient in the single natural binary SL₃ row has trivial commutant. -/
theorem source_natural_sl3_moved_commutant_card
    (a : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (e : sourceMovedQuotient D L ≃* Multiplicative (Fin 3 → ZMod 2))
    (he : ∀ k v, (e (sourceMovedQuotientAction D L L L.le_normalizer k v)).toAdd =
      (sourceMovedModelHom D a k).val.mulVec (e v).toAdd) :
    Nat.card (centralizer ((sourceMovedQuotientAction D L L L.le_normalizer).range :
      Set (MulAut (sourceMovedQuotient D L)))) = 1 :=
  binary_natural_commutant_card_eq_one (by decide) _
    (sourceMovedModelHom D a) (sourceMovedModelHom_surjective D a) e he

open ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The literal Hall kernel fixes the full module in the marked natural SL₂ row. -/
theorem source_hall_kernel_fixes_of_natural_sl2
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H)))
    {F : Type*} [Field F] [Finite F]
    (a : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (e : sourceMovedQuotient D L ≃* Multiplicative (Fin 2 → F))
    (he : ∀ k v, (e (sourceMovedQuotientAction D L L L.le_normalizer k v)).toAdd =
      (sourceMovedModelHom D a k).val.mulVec (e v).toAdd) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  apply source_hall_kernel_fixes_of_first_moved_commutant D hn Y hYM hY 1
  simpa only [pow_one] using source_natural_sl2_moved_commutant_dvd D a e he

/-- The literal Hall kernel fixes the full module in the marked natural binary SL₃ row. -/
theorem source_hall_kernel_fixes_of_natural_sl3
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H)))
    (a : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (e : sourceMovedQuotient D L ≃* Multiplicative (Fin 3 → ZMod 2))
    (he : ∀ k v, (e (sourceMovedQuotientAction D L L L.le_normalizer k v)).toAdd =
      (sourceMovedModelHom D a k).val.mulVec (e v).toAdd) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  apply source_hall_kernel_fixes_of_first_moved_commutant D hn Y hYM hY 0
  rw [source_natural_sl3_moved_commutant_card D a e he]
  exact one_dvd _
end CFSG.Quasithin.Chapter10
