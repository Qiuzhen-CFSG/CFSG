module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.CartanFixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Flag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Flag

/-!
# Reducing point geometry to the literal local two-core

Suppose R₁ is O₂(L₁)O₂(LT) and C_V(O₂(L₁))=V₁. The global core already
centralizes V. Hence C_V(R₁)=V₁. Every Cartan normalizes the point residual
and the global core, so it normalizes R₁. The proved Cartan fixed-space bound
then supplies exactly the existential geometry used by the corrected center
calculation, preserving the original flag and central kernel.

The two local-core identities are explicit, independent source obligations;
this module does not assert them or claim full source 11.1.5. Inner uniqueness
of the caller's flag is derived from the existing marked SL₃ and Sp₄ flags.
Source: Aschbacher–Smith, combined manuscript, 1 March 2004, 11.1.5,
printed pp.765–766, using the flag of printed pp.760–761.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Any original invariant flag in either block row has inner-Sylow uniqueness. -/
theorem block_flag_inner_unique {c : Coordinates D S.field} (f : InvariantFlag c)
    (hb : CFSG.Quasithin.ChapterC.IsSL3EvenBlock L S.field.degree ∨
      CFSG.Quasithin.ChapterC.IsSp4FourBlock L) : f.IsInnerUnique := by
  cases c with
  | sl3 m =>
    intro i U hd hn
    exact (SL3.flag_inner_unique D S m i U hd hn).trans
      (SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
        (inf_le_left.trans (f.invariant i))).symm
  | sp4 m =>
    intro i U hd hn
    exact (Sp4.flag_inner_unique m S i U hd hn).trans
      (Sp4.flag_inner_unique m S i (f.space i) (f.dimension i)
        (inf_le_left.trans (f.invariant i))).symm
  | g2 m => exact (no_g2_block_marking D S m hb).elim

/-- The local-core fixed space gives the full radical fixed space once its core product is known. -/
theorem point_centralizer_of_core_product {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hlocal : V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0) :
    V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0 := by
  have hcore : (f.Li 0).pCoreIn 2 ≤ f.Ri 0 := by
    rw [hprod]
    exact le_sup_left
  apply le_antisymm
  · exact (le_inf inf_le_left (inf_le_right.trans
      (centralizer_le hcore))).trans hlocal.le
  · intro v hv
    have h := hlocal.symm ▸ hv
    refine ⟨h.1, ?_⟩
    rw [hprod]
    apply le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mpr (show V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) ≤
        centralizer ((f.Li 0).pCoreIn 2 : Set G) from inf_le_right))
      (D.core_centralizes.trans (centralizer_le (show
        V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) ≤ V from inf_le_left)))) h

/-- The Cartan preserves both factors of the literal radical product. -/
theorem cartan_normalizes_point_radical_of_core_product
    {c : Coordinates D S.field} (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    {X : Subgroup G} (hX : IsCartan T L X) :
    X ≤ normalizer (f.Ri 0 : Set G) := by
  have hXL : X ≤ L := hX.1.trans inf_le_left
  have hn : X ≤ normalizer (f.Li 0 : Set G) :=
    ((le_inf (hXL.trans L.le_normalizer)
      ((f.cartan_normalizes hu hX 0).trans (normalizer _).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hq : X ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    ((hXL.trans le_sup_left).trans (L ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  rw [hprod]
  exact (le_inf (hn.trans (normalizer_le_normalizer_characteristic_image _
    (pCore 2 _))) hq).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The point geometry from two explicit local-core calculations. These calculations remain source obligations. -/
theorem exists_point_geometry_of_core_calculations
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hb : CFSG.Quasithin.ChapterC.IsSL3EvenBlock L S.field.degree ∨
      CFSG.Quasithin.ChapterC.IsSp4FourBlock L)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hlocal : V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0) :
    ∃ X : Subgroup G, IsCartan T L X ∧ X ≤ normalizer (f.Ri 0 : Set G) ∧
      (V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) ∧
      V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0 := by
  obtain ⟨X,hX⟩ := exists_cartan D
  exact ⟨X,hX,cartan_normalizes_point_radical_of_core_product D S f
    (block_flag_inner_unique D S f hb) hprod hX,
    block_cartan_fixed_le D S c hb hX, point_centralizer_of_core_product D S f hprod hlocal⟩

/-- The exact existential input consumed by the corrected point-cohomology center reduction. -/
theorem center_geometry_of_core_calculations
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hb : CFSG.Quasithin.ChapterC.IsSL3EvenBlock L S.field.degree ∨
      CFSG.Quasithin.ChapterC.IsSp4FourBlock L)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hlocal : V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0) :
    ∃ X : Subgroup G, X ≤ L ∧ X ≤ normalizer (f.Ri 0 : Set G) ∧
      Odd (Nat.card X) ∧ (V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) ∧
      V ⊓ centralizer (f.Ri 0 : Set G) = f.Vi 0 := by
  obtain ⟨X,hX,hn,hf,hp⟩ := exists_point_geometry_of_core_calculations D S f hb hprod hlocal
  exact ⟨X,hX.1.trans inf_le_left,hn,hX.odd,hf,hp⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry
