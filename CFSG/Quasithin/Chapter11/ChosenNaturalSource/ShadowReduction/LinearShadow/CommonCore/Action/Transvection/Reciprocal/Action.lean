module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Displacements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup

/-!
# The original reciprocal conjugation action

Pull the W action on the selected conjugate V^g back to V by the same g.
The representation intertwines the literal g⁻¹*w*g action with the original
chosen quotient. Its individual cyclic subgroups normalize V, have exponent
two, and their commutators are the inverse conjugates of the forward
commutators. No field linearity or source alignment is assumed.

Source: Aschbacher--Smith, 11.3.7(4), refs/quasithin.pdf, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

omit [Finite G] in
/-- Conjugating back and forward preserves the literal subgroup. -/
theorem map_conj_inv_conj (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
  rw [map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, MonoidHom.id_apply]
    group
  rw [he, map_id]

omit [Finite G] in
/-- The actual conjugate's normalization transports to the original seed. -/
theorem cyclic_normalizes_seed (g : G)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H) :
    (zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (V : Set G) := by
  have hcyc : zpowers (w : G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
    zpowers_le.mpr (hN w.property)
  have hn := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcyc).trans
    ((V.map (MulAut.conj g).toMonoidHom).le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  have hv : (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = V := by
    simpa only [inv_inv] using map_conj_inv_conj V g⁻¹
  rwa [hv] at hn

/-- The reciprocal actor on V, conjugated back by the original selected g. -/
def reciprocalNormalizerHom (g : G)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    omegaClosure T H →* normalizer (V : Set G) :=
  ((MulAut.conj g⁻¹).toMonoidHom.comp (omegaClosure T H).subtype).codRestrict _
    (fun w => cyclic_normalizes_seed g hN w
      (mem_map_of_mem _ (mem_zpowers (w : G))))

/-- The actual reciprocal conjugation representation, in the original marking.
Its actor w on V is g⁻¹*w*g, so this is the W action on V^g pulled back by g. -/
def reciprocalAction (c : Coordinates D S.field) (g : G)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Representation (ZMod 2) (omegaClosure T H) c.Space :=
  (c.conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl).comp
    (reciprocalNormalizerHom g hN)

/-- The representation retains the literal ambient conjugation. -/
theorem reciprocalAction_projection (c : Coordinates D S.field) (g : G)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H) (v : V) :
    reciprocalAction c g hN w (c.projection v).toAdd =
      (c.projection (V.normalizerMonoidHom (reciprocalNormalizerHom g hN w) v)).toAdd :=
  c.conjugationAction_projection _ _ _ _

omit [Finite G] in
/-- Transport the individual commutator using the original g in both factors. -/
theorem cyclic_commutator_eq (g : G) (w : omegaClosure T H) :
    ⁅(zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom, V⁆ =
      (⁅V.map (MulAut.conj g).toMonoidHom, zpowers (w : G)⁆ : Subgroup G).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  have hv : (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = V := by
    simpa only [inv_inv] using map_conj_inv_conj V g⁻¹
  rw [map_commutator, hv, commutator_comm]

/-- Involutivity survives both taking the cyclic subgroup and conjugating back. -/
theorem cyclic_square_eq_one (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (w : omegaClosure T H)
    (b : (zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom) : b ^ 2 = 1 := by
  obtain ⟨u, hu, he⟩ := b.property
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
  apply Subtype.ext
  change (b : G) ^ 2 = 1
  rw [← he, ← map_pow]
  have hs : ((w : G) ^ k) ^ 2 = 1 := by
    rw [← zpow_natCast, zpow_comm, zpow_natCast,
      show (w : G) ^ 2 = 1 from congrArg Subtype.val (n.square_eq_one w), one_zpow]
  rw [hs, map_one]

/-- Each cyclic reciprocal actor has commutator of order at most q.
For a noncentral actor the forward coordinates give equality; a central
actor gives the trivial commutator. -/
theorem cyclic_commutator_card_le (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (w : omegaClosure T H) :
    Nat.card (⁅(zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom, V⁆ : Subgroup G) ≤
      Nat.card S.field.Carrier := by
  rw [cyclic_commutator_eq, card_map_of_injective (MulAut.conj g⁻¹).injective]
  by_cases hw : (w : G) ∈ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)
  · have he : ⁅V.map (MulAut.conj g).toMonoidHom, zpowers (w : G)⁆ = ⊥ := by
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
      exact zpowers_le.mpr hw
    rw [he, Subgroup.card_bot]
    exact Nat.card_pos
  · exact (n.card_vector_commutator w hw).le

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
