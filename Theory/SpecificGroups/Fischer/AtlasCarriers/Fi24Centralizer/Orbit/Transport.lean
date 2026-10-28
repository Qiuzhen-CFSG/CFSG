module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Orbit.Actions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Bray.Results
/-!
# Literal Fi22 generator actions of the centralizing lifts

The two Bray words preserve the checked 3510-point set. Multiplication,
inversion and powers transport that action to the selected lifting words,
whose small permutations are the original Fi22 generators.
-/
public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.Orbit

private def Tracks (g : Carrier) (p : Equiv.Perm (Fin 3510)) : Prop :=
  ∀ i, inclusion g (point i) = point (p i)
private theorem Tracks.one : Tracks 1 1 := by intro i; rfl
private theorem Tracks.mul {g h : Carrier} {p q : Equiv.Perm (Fin 3510)}
    (hg : Tracks g p) (hh : Tracks h q) : Tracks (g*h) (p*q) := by
  intro i
  change inclusion g (inclusion h (point i)) = point (p (q i))
  rw [hh, hg]
private theorem Tracks.inv {g : Carrier} {p : Equiv.Perm (Fin 3510)}
    (hg : Tracks g p) : Tracks g⁻¹ p⁻¹ := by
  intro i
  apply (inclusion g).injective
  rw [map_inv, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply, hg,
    ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
private theorem Tracks.pow {g : Carrier} {p : Equiv.Perm (Fin 3510)}
    (hg : Tracks g p) (n : Nat) : Tracks (g^n) (p^n) := by
  induction n with
  | zero => simpa only [pow_zero] using Tracks.one
  | succ n ih => simpa only [pow_succ] using ih.mul hg

private theorem h0_tracks : Tracks h0 smallPerm0 := by
  intro i
  apply Fin.ext
  exact (Bray.h0_table (point i)).trans (tableH0_point i)
private theorem h1_tracks : Tracks h1 smallPerm1 := by
  intro i
  apply Fin.ext
  exact (Bray.h1_table (point i)).trans (tableH1_point i)

private theorem liftA_tracks : Tracks liftA smallLiftA :=
  (((((((((h0_tracks.pow 3).mul h1_tracks).mul (h0_tracks.pow 2)).mul h1_tracks).mul h0_tracks).mul h1_tracks).mul h0_tracks.inv).mul (h1_tracks.pow 2))).pow 15

private theorem liftB_tracks : Tracks liftB smallLiftB :=
  ((((((((((((((((((((((((h0_tracks.mul h1_tracks).mul h0_tracks).mul h1_tracks).mul (h0_tracks.pow 3)).mul h1_tracks.inv).mul (h0_tracks.pow 3)).mul h1_tracks.inv).mul h0_tracks).mul h1_tracks).mul h0_tracks).mul h1_tracks).mul (h0_tracks.pow 2)).mul h1_tracks).mul h0_tracks.inv).mul h1_tracks).mul h0_tracks.inv).mul h1_tracks).mul (h0_tracks.inv.pow 3)).mul h1_tracks).mul (h0_tracks.inv.pow 3)).mul h1_tracks.inv).mul h0_tracks.inv).mul h1_tracks.inv).mul h0_tracks.inv)

theorem liftA_action (i : Fin 3510) :
    inclusion liftA (point i) = point (Fi22.generatorA i) := by
  rw [← smallLiftA_eq]
  exact liftA_tracks i

theorem liftB_action (i : Fin 3510) :
    inclusion liftB (point i) = point (Fi22.generatorB i) := by
  rw [← smallLiftB_eq]
  exact liftB_tracks i
end Sporadic.Fischer.Fi24Prime.CentralizerSection.Orbit
