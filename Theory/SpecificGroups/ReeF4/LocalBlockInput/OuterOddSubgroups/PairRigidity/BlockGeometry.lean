module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.Parabolics
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.SplitGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat

/-!
# Generation and recognition of the four fixed Ree simple blocks

For `m ≥ 1`, the four signed simple blocks generate the simple fixed group.
Fixed collection puts the positive unipotent subgroup in their join and each
fixed seed in the join of that positive subgroup and its negative simple block.
The fixed-seed generation theorem then gives the whole fixed group.

For recognition, start with the intrinsic normalizers of the two unipotent
subgroups and adjoin one opposite simple block. The parabolic geometry proves
that these are precisely the two maximal overgroups of each normalizer and that
their sizes differ. Consequently a pair-preserving
automorphism fixes them individually. The opposite-parabolic intersection then
recovers each signed simple block. The intrinsic unipotent normalizers are
identified with the root Borels by the proved normalizer calculation.

The conditional assembly lemmas are retained; the final theorems discharge all
their geometric premises. Generation uses simplicity but needs neither
perfectness nor odd index. Recognition uses the supplied odd unipotent index
but needs neither simplicity nor perfectness.

Source: GLS3, §§2.3–2.5, especially 2.3.6–8 and 2.5.1. The positive blocks
are the actual A₁ × A₁ and B₂ fixed intersections defined in `PairRigidity.Basic`.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity
open Subgroup LargeLocalSeeds
variable {m : ℕ}

private theorem map_eq_of_two_coatoms {G : Type*} [Group G]
    (a : MulAut G) (B : Subgroup G) (P : Side → Subgroup G)
    (hB : B.map a.toMonoidHom = B)
    (hcoat : ∀ K, IsCoatom K ∧ B ≤ K ↔ ∃ s, K = P s)
    (hcard : Nat.card (P .suzuki) ≠ Nat.card (P .linear)) :
    ∀ s, (P s).map a.toMonoidHom = P s := by
  intro s
  have hP := (hcoat (P s)).mpr ⟨s, rfl⟩
  have hm : IsCoatom ((P s).map a.toMonoidHom) ∧ B ≤ (P s).map a.toMonoidHom := by
    refine ⟨(OrderIso.isCoatom_iff a.mapSubgroup _).mpr hP.1, ?_⟩
    rw [← hB]
    exact Subgroup.map_mono hP.2
  obtain ⟨t, ht⟩ := (hcoat _).mp hm
  have he : Nat.card (P t) = Nat.card (P s) := by
    rw [← ht]
    exact Subgroup.card_map_of_injective a.injective
  cases s <;> cases t
  · exact ht
  · exact False.elim (hcard he.symm)
  · exact False.elim (hcard he)
  · exact ht

/-- Maximal-overgroup recognition and opposite intersections imply individual block
preservation. The cardinal inequality prevents interchanging the two sides.
All three fixed-group geometric assertions remain explicit inputs. -/
theorem preservesSimpleBlocks_of_parabolic_geometry (d : LocalBlockInput m)
    (hmax : ∀ positive P,
      IsCoatom P ∧ signedBorelNormalizer d positive ≤ P ↔
        ∃ s, P = signedParabolic d s positive)
    (hcard : ∀ positive, Nat.card (signedParabolic d .suzuki positive) ≠
      Nat.card (signedParabolic d .linear positive))
    (hinter : ∀ s positive,
      signedUnipotent d positive ⊓ signedParabolic d s (!positive) = simpleBlock d s positive)
    (a : MulAut d.fixedGroup) (ha : d.PreservesUnipotentPair a) :
    PreservesSimpleBlocks d a := by
  have hP (positive : Bool) : ∀ s,
      (signedParabolic d s positive).map a.toMonoidHom = signedParabolic d s positive :=
    map_eq_of_two_coatoms a (signedBorelNormalizer d positive)
      (fun s => signedParabolic d s positive) (signedBorelNormalizer_map d a ha positive)
      (hmax positive) (hcard positive)
  intro s positive
  rw [← hinter s positive, Subgroup.map_inf _ _ _ a.injective,
    signedUnipotent_map d a ha, hP]

/-- Assemble fixed-block generation from fixed-seed generation and collection.
The positive unipotent subgroup must be collected into the four signed blocks,
and each fixed seed into the positive subgroup and its negative simple block. -/
theorem simpleBlocks_generate_of_seed_collection (d : LocalBlockInput m)
    (hseeds : standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤)
    (hcollection : ∀ s, standardSeed d s ≤
      standardUnipotent d ⊔ simpleBlock d s false)
    (hpositive : standardUnipotent d ≤ ⨆ s, ⨆ positive, simpleBlock d s positive) :
    (⨆ s, ⨆ positive, simpleBlock d s positive) = ⊤ := by
  have hseed (s : Side) : standardSeed d s ≤ ⨆ s, ⨆ positive, simpleBlock d s positive :=
    (hcollection s).trans (sup_le hpositive
      (le_iSup_of_le s (le_iSup (fun positive => simpleBlock d s positive) false)))
  apply top_unique
  rw [← hseeds]
  exact sup_le (hseed .suzuki) (hseed .linear)

/-- The four actual signed simple fixed blocks generate the simple fixed group.
The fixed-seed and fixed-collection theorems discharge every premise of the
generation reduction; no preservation of joins by fixed points is used. -/
theorem simpleBlocks_generate (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] :
    (⨆ s, ⨆ positive, simpleBlock d s positive) = ⊤ :=
  simpleBlocks_generate_of_seed_collection d (FixedBruhat.standardSeed_sup_eq_top d)
    (FixedCollection.standardSeed_le_unipotent_sup_negativeBlock hm d)
    (FixedCollection.standardUnipotent_le_iSup_simpleBlock d)

/-- An automorphism preserving the specified positive and opposite unipotent
subgroups preserves each simple fixed block individually. The distinct
parabolic orders prevent interchanging the Suzuki and linear sides. -/
theorem preservesSimpleBlocks_of_preservesUnipotentPair (hm : 1 ≤ m)
    (d : LocalBlockInput m) (hindex : Odd (standardUnipotent d).index)
    (a : MulAut d.fixedGroup) (ha : d.PreservesUnipotentPair a) :
    PreservesSimpleBlocks d a :=
  preservesSimpleBlocks_of_parabolic_geometry d (signedParabolic_maximal_overgroups d)
    (signedParabolic_card_ne hm d hindex)
    (signedUnipotent_inf_opposite_signedParabolic d) a ha

end ReeF4.LocalBlockInput.PairRigidity
end
