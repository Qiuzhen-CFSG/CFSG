module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsBinary
public import Theory.SpecificGroups.PSL2.BinaryPerfectCentralizer

/-!
# Elimination of the binary rank-one row in the nonblock sieve

Transport the literal secondary projection to a binary PSL₂ model. Its
perfect inner image has trivial two-core, so the mutually normalizing
radical image centralizes it. The torus also centralizes it by the proved
core-image calculation. Both images therefore lie in a cyclic centralizer,
and the original identity [R₂-star,Y-star] = R₂-star forces R₂-star = 1.
The prescribed nontrivial radical action excludes every binary PSL₂ model,
in particular original 4.3.16(1). No subfield marking is assumed.

Source: Aschbacher–Smith, original 4.3.15--16 and the following elimination,
printed p.618. The other model rows remain separate local obligations.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The actual projection is nontrivial because its two-core quotient is PSL₂. -/
theorem SecondaryData.secondaryProjection_ne_bot (s : SecondaryData c n) :
    (SecondaryData.secondaryProjection s).range ≠ ⊥ := by
  obtain ⟨E, _, _, _, ⟨e⟩⟩ := SecondaryData.secondaryProjection_model s
  let : Nontrivial ((SecondaryData.secondaryProjection s).range ⧸
      pCore 2 (SecondaryData.secondaryProjection s).range) := e.surjective.nontrivial
  let : Nontrivial (SecondaryData.secondaryProjection s).range :=
    (QuotientGroup.mk'_surjective (pCore 2 (SecondaryData.secondaryProjection s).range)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

/-- The cyclic perfect-subgroup centralizer kills the entire literal radical image. -/
theorem SecondaryData.radicalImage_eq_bot_of_binary (s : SecondaryData c n)
    {m : ℕ} (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (2 ^ m)) :
    SecondaryData.radicalImage s = ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let A := MulAut.congr e
  let H := (SecondaryData.secondaryProjection s).range
  let H' := H.map e.toMonoidHom
  let R' := (SecondaryData.radicalImage s).map A.toMonoidHom
  let Y' := (SecondaryData.torusImage s).map A.toMonoidHom
  let := SecondaryData.secondaryProjection_perfect s
  let : Group.IsPerfect H' := Group.IsPerfect.map _
  have hn : H' ≠ ⊥ := fun he => SecondaryData.secondaryProjection_ne_bot s
    ((H.map_eq_bot_iff_of_injective e.injective).mp he)
  have hmap : (SecondaryData.secondaryImage s).map A.toMonoidHom = H'.map MulAut.conj := by
    rw [show SecondaryData.secondaryImage s = H.map MulAut.conj from
      SecondaryData.secondary_action_image s]
    rw [map_map, show H' = H.map e.toMonoidHom from rfl, map_map]
    congr 1
    exact MonoidHom.ext (fun x => MulAut.congr_conj e x)
  have hnorm := SecondaryData.image_normalization s
  have hHR : H'.map MulAut.conj ≤ normalizer (R' : Set (MulAut (Theory.PSL2.Group F))) := by
    rw [← hmap]
    exact (map_mono hnorm.1).trans ((SecondaryData.radicalImage s).le_normalizer_map _)
  have hRH : R' ≤ normalizer (H'.map MulAut.conj : Set (MulAut (Theory.PSL2.Group F))) := by
    rw [← hmap]
    exact (map_mono hnorm.2.1).trans ((SecondaryData.secondaryImage s).le_normalizer_map _)
  have hY : Y' ≤ centralizer (H'.map MulAut.conj : Set (MulAut (Theory.PSL2.Group F))) := by
    rw [← hmap]
    exact (map_mono (SecondaryData.torusImage_centralizes_of_binary s
      ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩)).trans (map_centralizer_le_centralizer_image _ _)
  have hmove : ⁅R',Y'⁆ = R' := by
    rw [show R' = (SecondaryData.radicalImage s).map A.toMonoidHom from rfl,
      show Y' = (SecondaryData.torusImage s).map A.toMonoidHom from rfl,
      ← map_commutator, SecondaryData.radicalImage_moved]
  have hr := Theory.PSL2.twoGroup_eq_bot_of_moved_by_centralizer H' hn R' Y'
    ((SecondaryData.radicalImage_two s).1.map _) hHR hRH hY hmove
  exact ((SecondaryData.radicalImage s).map_eq_bot_iff_of_injective A.injective).mp hr

/-- No binary PSL₂ model is compatible with the original nontrivial radical action. -/
theorem SecondaryData.not_binary_model (s : SecondaryData c n) (m : ℕ) :
    ¬ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (2 ^ m) := by
  intro hm
  exact (SecondaryData.radicalImage_two s).2 (SecondaryData.radicalImage_eq_bot_of_binary s hm)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
