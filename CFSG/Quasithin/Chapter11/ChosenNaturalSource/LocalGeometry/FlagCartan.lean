module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.RadicalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.RadicalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Orbits
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry

/-!
# The unique marked natural flag and the source Cartan

Each actual SL₃, Sp₄ or G₂ marking supplies the invariant flag, its uniqueness
under both the ambient and inner Sylow, and the literal local PSL₂ quotients.
The actual locals generate L. Inner uniqueness discharges the Cartan geometry
premise, so the resulting existence theorem assumes neither a flag nor a Cartan.
It includes flag normalization and prime rank two for primes dividing q − 1.
The corrected plane geometry also supplies normalizer control on this same
flag, retaining only the earlier unique noncentral-component premise of
11.1.3. Its producer is qt-d-1222-natural-relative-components; source
assembly and final discharge remain with qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, 11.0.2--4 and the opening of §11.1,
printed pp.759--761. Further local action and orbit identities live in the
marked-family extension modules.
-/

@[expose] public noncomputable section


open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

theorem exists_unique_marked_flag (c : Coordinates D S.field) :
    ∃ f : InvariantFlag c, f.IsUnique ∧ f.IsInnerUnique ∧
      (∀ i : Fin 2, Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier))) ∧
      L = f.Li 0 ⊔ f.Li 1 := by
  cases c with
  | sl3 m =>
    exact ⟨SL3.flag D S m, SL3.flag_unique D S m, SL3.flag_inner_unique D S m,
      fun i => ⟨SL3.flagLocalCoreEquiv S m (SL3.flag D S m) i⟩,
      SL3.PlaneAction.locals_generate D S m⟩
  | sp4 m =>
    exact ⟨Sp4.flag m S, Sp4.flag_unique m S, Sp4.flag_inner_unique m S,
      fun i => ⟨Sp4.source_Li_quotientEquiv S m i⟩, Sp4.source_Li_sup S m⟩
  | g2 m =>
    exact ⟨G2.flag S m, G2.flag_unique S m, G2.flag_inner_unique S m,
      fun i => ⟨G2.ResidualIncidence.flag_Li_quotientEquiv S m i⟩,
      (G2.ResidualIncidence.flag_Li_sup S m).symm⟩

theorem exists_unique_source_flag_and_cartan :
    ∃ (f : InvariantFlag (coordinates D S)) (X : Subgroup G),
      f.IsUnique ∧ f.IsInnerUnique ∧
      (∀ i : Fin 2, Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier))) ∧
      L = f.Li 0 ⊔ f.Li 1 ∧ IsCartan T L X ∧
      (∀ i : Fin 3, X ≤ normalizer (f.Vi i : Set G)) ∧
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → primeRank p X = 2 := by
  obtain ⟨f,hf,hi,hq,hg⟩ := exists_unique_marked_flag D S (coordinates D S)
  obtain ⟨X,hX,hn,hr⟩ := exists_cartan_geometry S f hi
  exact ⟨f,X,hf,hi,hq,hg,hX,hn,hr⟩

/-- All marked families supply the same flag and the geometric input to 11.1.4.
Only the preceding component-uniqueness conclusion of 11.1.3 remains explicit. -/
theorem exists_marked_flag_with_normalizerControl (c : Coordinates D S.field) :
    ∃ f : InvariantFlag c, f.IsUnique ∧ f.IsInnerUnique ∧
      (∀ i : Fin 2, Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier))) ∧
      L = f.Li 0 ⊔ f.Li 1 ∧
      (Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) →
        Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G))) := by
  cases c with
  | sl3 m =>
    refine ⟨SL3.flag D S m,SL3.flag_unique D S m,SL3.flag_inner_unique D S m,
      fun i => ⟨SL3.flagLocalCoreEquiv S m (SL3.flag D S m) i⟩,
      SL3.PlaneAction.locals_generate D S m,?_⟩
    intro _
    exact Normalizers.chosen_normalizerControl_of_top D S (SL3.flag D S m)
      (InvariantFlag.sl3_top m (SL3.flag D S m))
  | sp4 m =>
    exact ⟨Sp4.flag m S,Sp4.flag_unique m S,Sp4.flag_inner_unique m S,
      fun i => ⟨Sp4.source_Li_quotientEquiv S m i⟩,Sp4.source_Li_sup S m,
      Sp4.Orbits.source_normalizerControl S m⟩
  | g2 m =>
    exact ⟨G2.flag S m,G2.flag_unique S m,G2.flag_inner_unique S m,
      fun i => ⟨G2.ResidualIncidence.flag_Li_quotientEquiv S m i⟩,
      (G2.ResidualIncidence.flag_Li_sup S m).symm,
      G2.ResidualIncidence.source_normalizerControl S m⟩

/-- The source's constructed flag and Cartan carry the actual normalizer-control
application. The component owner supplies the remaining 11.1.3 premise. -/
theorem exists_source_flag_cartan_with_normalizerControl :
    ∃ (f : InvariantFlag (coordinates D S)) (X : Subgroup G),
      f.IsUnique ∧ f.IsInnerUnique ∧
      (∀ i : Fin 2, Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier))) ∧
      L = f.Li 0 ⊔ f.Li 1 ∧ IsCartan T L X ∧
      (∀ i : Fin 3, X ≤ normalizer (f.Vi i : Set G)) ∧
      (∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → primeRank p X = 2) ∧
      (Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) →
        Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G))) := by
  obtain ⟨f,hf,hi,hq,hg,hcontrol⟩ := exists_marked_flag_with_normalizerControl D S (coordinates D S)
  obtain ⟨X,hX,hn,hr⟩ := exists_cartan_geometry S f hi
  exact ⟨f,X,hf,hi,hq,hg,hX,hn,hr,hcontrol⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
