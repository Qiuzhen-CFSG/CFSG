module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveContracts
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Core-image centrality in the binary rank-one row

Every homomorphism from a perfect group into binary SL₂ kills its two-core:
a nontrivial normal two-subgroup would force the image into a solvable Borel.
Apply this to the literal secondary projection, after transporting the
actual PSL₂ model to SL₂. Thus the original secondary core has trivial
inner-action image, and perfectness lifts the torus commutator bound to
centralization of all K₂-star.

This proves the centralization step in row (1), not its prime-order
automorphism exclusion. The other rows and the full sieve remain open.
Source: Aschbacher--Smith, first paragraph after 4.3.16, printed p.618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- In a binary PSL₂ component quotient, the actual secondary two-core acts trivially. -/
theorem SecondaryData.secondaryCoreImage_eq_bot_of_binary (s : SecondaryData c n)
    {m : ℕ} (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (2 ^ m)) :
    SecondaryData.secondaryCoreImage s = ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := ((Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm.toMonoidHom.comp
    e.toMonoidHom).comp (SecondaryData.secondaryProjection s)
  let := secondary_perfect c
  have hk := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker f
  apply (eq_bot_iff_forall _).mpr
  rintro a ⟨x,hx,rfl⟩
  obtain ⟨y,hy,he⟩ := hx
  have hp : SecondaryData.secondaryProjection s y = 1 := by
    apply e.injective
    apply (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm.injective
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_one] using
      (show f y = 1 from hk hy)
  have hxy : x = ⟨y, (s.secondary_le.trans (map_subtype_le _)) y.property⟩ :=
    Subtype.ext he.symm
  rw [hxy,SecondaryData.action_secondary,hp,map_one]

/-- The binary row satisfies the exact core-image centrality premise. -/
theorem SecondaryData.coreImageCentral_of_binary (s : SecondaryData c n)
    {m : ℕ} (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (2 ^ m)) :
    SecondaryData.CoreImageCentral s := by
  change SecondaryData.secondaryCoreImage s ≤ _
  rw [SecondaryData.secondaryCoreImage_eq_bot_of_binary s hm]
  exact bot_le

/-- The actual torus centralizes the entire secondary image in the binary row. -/
theorem SecondaryData.torusImage_centralizes_of_binary (s : SecondaryData c n)
    {m : ℕ} (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (2 ^ m)) :
    SecondaryData.torusImage s ≤ centralizer (SecondaryData.secondaryImage s : Set _) :=
  SecondaryData.torusImage_centralizes_of_coreImageCentral s
    (SecondaryData.coreImageCentral_of_binary s hm)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

end
