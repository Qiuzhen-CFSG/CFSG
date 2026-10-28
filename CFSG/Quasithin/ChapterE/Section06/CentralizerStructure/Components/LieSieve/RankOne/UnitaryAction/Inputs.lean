module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Sylow

/-!
# Intrinsic inputs for the PSU₃ Borel calculation

The marked Sylow center and its Borel action live in the actual group, before
embedding that group in an E.6 configuration. Two independent model statements
suffice: an involutory automorphism fixing the Borel pointwise is trivial, and
the Borel acts irreducibly on the Sylow center with cyclic image of order q−1.
The declarations below specify these obligations; they do not assert them.

Characteristicity proves normalization of the center, and an actual group
isomorphism transports the Borel-fixer statement. The ambient assembly uses
these interfaces to identify its fixed space and displacement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1),
printed pp.247–248; Huppert II.10.12 for the intrinsic unitary root and torus.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction

variable {G H : Type*} [Group G] [Group H]

/-- The center of the marked Sylow subgroup, embedded in its original group. -/
def sylowCenter (S : Sylow 2 H) : Subgroup H :=
  (center S).map (S : Subgroup H).subtype

/-- The intrinsic pointwise Borel fixer has no nonidentity involution.
This is an obligation on the actual automorphism group, not an E.6 hypothesis. -/
def BorelRigid (S : Sylow 2 H) : Prop :=
  ∀ a : MulAut H, a ^ 2 = 1 →
    (∀ b ∈ normalizer (S : Set H), a b = b) → a = 1

/-- The two intrinsic action facts needed from the unitary model: irreducibility
on its Sylow center and the actual cyclic image of the Borel on that center.
Neither clause refers to the external group V or assumes its displacement. -/
structure CenterAction (S : Sylow 2 H) (n : ℕ) : Prop where
  irreducible : ∀ A : Subgroup H, A ≤ sylowCenter S →
    normalizer (S : Set H) ≤ normalizer (A : Set H) →
      A = ⊥ ∨ A = sylowCenter S
  cyclic_image : Nonempty (inducedAutomizer (sylowCenter S)
    (normalizer (S : Set H)) ≃* Multiplicative (ZMod (2 ^ n - 1)))

/-- The normalizer preserves the embedded Sylow center by characteristicity. -/
theorem sylowCenter_normalized (S : Sylow 2 H) :
    normalizer (S : Set H) ≤ normalizer (sylowCenter S : Set H) :=
  normalizer_le_normalizer_characteristic_image (S : Subgroup H) (center S)

/-- Transport pointwise Borel rigidity through an actual model equivalence. -/
theorem BorelRigid.of_equiv [Finite G] (S : Sylow 2 G) (e : G ≃* H)
    (hr : BorelRigid (S.mapSurjective (f := e.toMonoidHom) e.surjective)) :
    BorelRigid S := by
  intro a ha hfix
  apply (MulAut.congr e).injective
  rw [map_one]
  apply hr _ (by rw [← map_pow, ha, map_one])
  intro b hb
  have hb' : b ∈ (normalizer (S : Set G)).map e.toMonoidHom := by
    change b ∈ (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom
    rw [Subgroup.map_equiv_normalizer_eq]
    exact hb
  obtain ⟨c, hc, rfl⟩ := hb'
  change e (a (e.symm (e c))) = e c
  rw [e.symm_apply_apply, hfix c hc]

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction
