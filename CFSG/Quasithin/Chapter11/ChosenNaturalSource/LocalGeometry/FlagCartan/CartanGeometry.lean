module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# The source Cartan geometry for a marked natural flag

For the literal chosen component and its marked natural action, every Cartan
normalizes an inner-unique flag and has prime rank two at every prime dividing
q - 1. Schur--Zassenhaus supplies such a Cartan in the original N_L(T_L).
The same Cartan now discharges the normalization and rank inputs of the
11.5.6(1) coprimality argument in each actual flag normalizer.

The only geometric premise is the precise uniqueness under T intersect L.
Flag construction and its uniqueness are discharged by the independent
marked-flag producers in the parent natural-flag assembly.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Chapter 11 opening and 11.0.4, the normalization preceding 11.1.2,
and 11.5.6(1), printed pp.759--761,780.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The full conditional Cartan contract, with the original Hall condition,
all three flag normalizers, and exact prime rank. -/
theorem exists_cartan_geometry (hu : f.IsInnerUnique) :
    ∃ X : Subgroup G, IsCartan T L X ∧
      (∀ i : Fin 3, X ≤ normalizer (f.Vi i : Set G)) ∧
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → primeRank p X = 2 := by
  obtain ⟨X, hX⟩ := exists_cartan D
  exact ⟨X, hX, f.cartan_normalizes hu hX, fun _ hp hd => c.cartan_primeRank hX hp hd⟩

/-- In the actual flag-normalizer consumer, geometry removes both the
Cartan-normalization and prime-rank assumptions of 11.5.6(1). -/
theorem flag_cartan_coprime_of_inner_unique (hu : f.IsInnerUnique)
    (i : Fin 3) {X Y : Subgroup G} (hX : IsCartan T L X)
    (hY : Y ≤ normalizer (f.Vi i : Set G))
    (hn : X ≤ normalizer (Y : Set G)) (hd : Disjoint X Y) :
    Nat.Coprime (Nat.card Y) (2 ^ S.field.degree - 1) :=
  flag_cartan_coprime S f i X Y (f.cartan_normalizes hu hX i) hY
    (fun _ hp hpq => (c.cartan_primeRank hX hp hpq).ge) hn hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
