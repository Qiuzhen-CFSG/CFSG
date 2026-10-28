module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.RootGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.Recognition.LinearBlock
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition

/-!
# Generation and recognition of the canonical Ree root blocks

The matrix-preserving model equivalence transports pair and block preservation
in both directions. Fixed collection, combined with the supplied generation by
the two canonical seeds, yields generation by the four canonical blocks. Thus
this reduction does not ask for a second fixed-seed-generation theorem.

An opposition double-coset factorization supplies the inner correction on the
unipotent pair. The two maximal parabolics are then individually fixed because
their orders differ; intersection with the opposite unipotent subgroup recovers
the signed blocks. These steps transport the actual fixed intersections,
including the full B₂ subgroup on the Suzuki side.

The final theorems discharge the collection, opposition-cell and parabolic
geometry premises of the retained reductions. Generation uses `1 ≤ m` and the
supplied seed generation. Recognition uses `1 ≤ m` and the supplied odd
unipotent index. The finite type V Suzuki block and type VI linear block have
respectively `q²` and `q` elements, where `q = 2^(2*m+1)`. Their proved rank-one
relations give parabolic indices `q² + 1` and `q + 1`, preventing an automorphism
from exchanging the two sides. This is the finite cardinality argument in
Steinberg's Theorem 36; it retains the nonabelian Suzuki multiplication law.

No simplicity, perfectness or automorphism-coverage assumption is used. Pair
normalization and block recognition apply to every automorphism preserving the
positive subgroup, so they do not need a two-power-order hypothesis. No order
is asserted for the left-corrected automorphism.

`Recognition.LinearBlock` proves that the entire positive linear block is
commutative of exponent two. `Recognition.BlockOpposition` separately proves
opposition on the full fixed blocks and signed parabolic candidates.

Source: GLS3, §§2.3–2.5, especially 2.3.8, Table 2.4 and 2.5.1;
`refs/KGroup/GLS3/Chapter2St1.tex`, Theorem 36; the application is
Aschbacher–Smith F.1.12, printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
open Subgroup LargeLocalSeeds

private theorem map_aut_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a : MulAut G) (K : Subgroup G) :
    (K.map e.toMonoidHom).map ((MulAut.congr e) a).toMonoidHom =
      (K.map a.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

private theorem congr_conj {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g : G) :
    (MulAut.congr e) (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

/-- Pair preservation is invariant under the actual matrix-preserving comparison. -/
theorem modelEquiv_preservesUnipotentPair_iff {m : ℕ} (d : LocalBlockInput m)
    (a : MulAut d.fixedGroup) :
    PreservesUnipotentPair m ((MulAut.congr d.modelEquiv) a) ↔
      LocalBlockInput.PreservesUnipotentPair d a := by
  unfold PreservesUnipotentPair LocalBlockInput.PreservesUnipotentPair
  rw [← modelEquiv_map_standardUnipotent d, ← modelEquiv_map_oppositeUnipotent d,
    map_aut_congr, map_aut_congr]
  exact and_congr (Subgroup.map_injective d.modelEquiv.injective).eq_iff
    (Subgroup.map_injective d.modelEquiv.injective).eq_iff

/-- Individual preservation of the four fixed blocks is preserved and reflected. -/
theorem modelEquiv_preservesSimpleBlocks_iff {m : ℕ} (d : LocalBlockInput m)
    (a : MulAut d.fixedGroup) :
    PreservesSimpleBlocks m ((MulAut.congr d.modelEquiv) a) ↔
      LocalBlockInput.PairRigidity.PreservesSimpleBlocks d a := by
  unfold PreservesSimpleBlocks LocalBlockInput.PairRigidity.PreservesSimpleBlocks
  apply forall_congr'
  intro s
  apply forall_congr'
  intro positive
  rw [← modelEquiv_map_simpleBlock d, map_aut_congr]
  exact (Subgroup.map_injective d.modelEquiv.injective).eq_iff

/-- The supplied canonical seed generation and two fixed collection statements
suffice for generation by the four canonical blocks. -/
theorem simpleBlocks_generate_of_collection {m : ℕ} (d : LocalBlockInput m)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    (hcollection : ∀ s, standardSeed d s ≤ standardUnipotent d ⊔
      LocalBlockInput.PairRigidity.simpleBlock d s false)
    (hpositive : standardUnipotent d ≤
      ⨆ s, ⨆ positive, LocalBlockInput.PairRigidity.simpleBlock d s positive) :
    (⨆ s, ⨆ positive, simpleBlock m s positive) = ⊤ := by
  have hseeds : standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤ := by
    apply Subgroup.map_injective (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective
    simpa only [Subgroup.map_sup, modelEquiv_map_standardSeed,
      Subgroup.map_top_of_surjective d.modelEquiv.toMonoidHom d.modelEquiv.surjective]
      using hgen
  exact simpleBlocks_generate_of_standard d
    (LocalBlockInput.PairRigidity.simpleBlocks_generate_of_seed_collection
      d hseeds hcollection hpositive)

/-- Transport the opposition-cell correction to the canonical group. The fixed
opposition representative and double-coset criterion are explicit inputs. -/
theorem exists_inner_adjustment_of_standard_opposition_cell {m : ℕ}
    (d : LocalBlockInput m) (w : d.fixedGroup)
    (hw : (standardUnipotent d).map (MulAut.conj w).toMonoidHom =
      LocalBlockInput.oppositeUnipotent d)
    (hcell : ∀ x : d.fixedGroup,
      Disjoint (standardUnipotent d)
        ((standardUnipotent d).map (MulAut.conj x).toMonoidHom) →
      ∃ u ∈ normalizer (standardUnipotent d),
      ∃ v ∈ normalizer (standardUnipotent d), x = u * w * v)
    (b : MulAut (Model m))
    (hU : (unipotent m).map b.toMonoidHom = unipotent m) :
    ∃ g : Model m, PreservesUnipotentPair m ((MulAut.conj g)⁻¹ * b) := by
  let e := MulAut.congr d.modelEquiv
  let a := e.symm b
  have hea : (MulAut.congr d.modelEquiv) a = b := e.apply_symm_apply b
  have ha : (standardUnipotent d).map a.toMonoidHom = standardUnipotent d := by
    apply Subgroup.map_injective (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective
    rw [← map_aut_congr, modelEquiv_map_standardUnipotent]
    simpa only [hea] using hU
  obtain ⟨g, hg⟩ :=
    LocalBlockInput.exists_inner_adjustment_preserving_pair_of_opposition_cell d w hw hcell a ha
  refine ⟨d.modelEquiv g, ?_⟩
  have h := (modelEquiv_preservesUnipotentPair_iff d ((MulAut.conj g)⁻¹ * a)).mpr hg
  simpa only [map_mul, map_inv, congr_conj, hea] using h

/-- Recognize canonical blocks using maximal parabolics, their different orders,
and the exact opposite-parabolic intersections in a supplied fixed group. -/
theorem preservesSimpleBlocks_of_standard_parabolic_geometry {m : ℕ}
    (d : LocalBlockInput m)
    (hmax : ∀ positive P, IsCoatom P ∧
      LocalBlockInput.PairRigidity.signedBorelNormalizer d positive ≤ P ↔
        ∃ s, P = LocalBlockInput.PairRigidity.signedParabolic d s positive)
    (hcard : ∀ positive,
      Nat.card (LocalBlockInput.PairRigidity.signedParabolic d .suzuki positive) ≠
        Nat.card (LocalBlockInput.PairRigidity.signedParabolic d .linear positive))
    (hinter : ∀ s positive,
      LocalBlockInput.PairRigidity.signedUnipotent d positive ⊓
        LocalBlockInput.PairRigidity.signedParabolic d s (!positive) =
          LocalBlockInput.PairRigidity.simpleBlock d s positive)
    (b : MulAut (Model m)) (hb : PreservesUnipotentPair m b) :
    PreservesSimpleBlocks m b := by
  let e := MulAut.congr d.modelEquiv
  let a := e.symm b
  have hea : e a = b := e.apply_symm_apply b
  have ha := (modelEquiv_preservesUnipotentPair_iff d a).mp (hea.symm ▸ hb)
  have hblocks := LocalBlockInput.PairRigidity.preservesSimpleBlocks_of_parabolic_geometry
    d hmax hcard hinter a ha
  exact hea ▸ (modelEquiv_preservesSimpleBlocks_iff d a).mpr hblocks

/-- Conditional assembly of pair and block preservation after one inner correction.
Each geometric premise must be discharged to obtain the source recognition result. -/
theorem exists_pair_and_blocks_of_standard_geometry {m : ℕ}
    (d : LocalBlockInput m) (w : d.fixedGroup)
    (hw : (standardUnipotent d).map (MulAut.conj w).toMonoidHom =
      LocalBlockInput.oppositeUnipotent d)
    (hcell : ∀ x : d.fixedGroup,
      Disjoint (standardUnipotent d)
        ((standardUnipotent d).map (MulAut.conj x).toMonoidHom) →
      ∃ u ∈ normalizer (standardUnipotent d),
      ∃ v ∈ normalizer (standardUnipotent d), x = u * w * v)
    (hmax : ∀ positive P, IsCoatom P ∧
      LocalBlockInput.PairRigidity.signedBorelNormalizer d positive ≤ P ↔
        ∃ s, P = LocalBlockInput.PairRigidity.signedParabolic d s positive)
    (hcard : ∀ positive,
      Nat.card (LocalBlockInput.PairRigidity.signedParabolic d .suzuki positive) ≠
        Nat.card (LocalBlockInput.PairRigidity.signedParabolic d .linear positive))
    (hinter : ∀ s positive,
      LocalBlockInput.PairRigidity.signedUnipotent d positive ⊓
        LocalBlockInput.PairRigidity.signedParabolic d s (!positive) =
          LocalBlockInput.PairRigidity.simpleBlock d s positive)
    (b : MulAut (Model m))
    (hU : (unipotent m).map b.toMonoidHom = unipotent m) :
    ∃ g : Model m, PreservesUnipotentPair m ((MulAut.conj g)⁻¹ * b) ∧
      PreservesSimpleBlocks m ((MulAut.conj g)⁻¹ * b) := by
  obtain ⟨g, hg⟩ := exists_inner_adjustment_of_standard_opposition_cell d w hw hcell b hU
  exact ⟨g, hg, preservesSimpleBlocks_of_standard_parabolic_geometry
    d hmax hcard hinter _ hg⟩

/-- The four actual signed fixed blocks generate the canonical Ree group.
Fixed collection discharges both inclusions, using the supplied seed generation.
Odd index is unnecessary for this assertion. -/
theorem simpleBlocks_generate {m : ℕ} (hm : 1 ≤ m)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤) :
    (⨆ s, ⨆ positive, simpleBlock m s positive) = ⊤ := by
  let d := canonicalLocalBlockInput m
  exact simpleBlocks_generate_of_collection d hgen
    (LocalBlockInput.PairRigidity.FixedCollection.standardSeed_le_unipotent_sup_negativeBlock hm d)
    (LocalBlockInput.PairRigidity.FixedCollection.standardUnipotent_le_iSup_simpleBlock d)

/-- Fixed Weyl opposition and the Bruhat opposition cell supply an inner
correction preserving both canonical unipotent subgroups. -/
theorem exists_inner_adjustment_preserving_pair {m : ℕ} (hm : 1 ≤ m)
    (b : MulAut (Model m))
    (hU : (unipotent m).map b.toMonoidHom = unipotent m) :
    ∃ g : Model m, PreservesUnipotentPair m ((MulAut.conj g)⁻¹ * b) := by
  let d := canonicalLocalBlockInput m
  obtain ⟨w, hw⟩ := LocalBlockInput.PairNormalization.exists_opposition d
  exact exists_inner_adjustment_of_standard_opposition_cell d w hw
    (LocalBlockInput.PairNormalization.OppositionCell.exists_normalizer_factors_of_disjoint
      hm d w hw) b hU

/-- An automorphism preserving the actual opposite unipotent subgroups fixes
each full signed simple block. The two intrinsic parabolics are recognized by
maximality and their distinct orders, and their opposite intersections recover
the blocks. All geometric premises are discharged. -/
theorem preservesSimpleBlocks_of_pair {m : ℕ} (hm : 1 ≤ m)
    (hindex : Odd (unipotent m).index)
    (b : MulAut (Model m)) (hb : PreservesUnipotentPair m b) :
    PreservesSimpleBlocks m b := by
  let d := canonicalLocalBlockInput m
  have hindex' : Odd (standardUnipotent d).index := by
    rw [← Subgroup.index_map_equiv (standardUnipotent d) d.modelEquiv]
    change Odd ((standardUnipotent d).map d.modelEquiv.toMonoidHom).index
    rw [modelEquiv_map_standardUnipotent]
    exact hindex
  exact preservesSimpleBlocks_of_standard_parabolic_geometry d
    (LocalBlockInput.PairRigidity.signedParabolic_maximal_overgroups d)
    (LocalBlockInput.PairRigidity.signedParabolic_card_ne hm d hindex')
    (LocalBlockInput.PairRigidity.signedUnipotent_inf_opposite_signedParabolic d) b hb

/-- One inner correction preserves the unipotent pair and all four signed
simple blocks. This holds for every positive-subgroup-preserving automorphism;
neither seed generation nor a two-power-order assumption is needed here. -/
theorem exists_inner_adjustment_preserving_pair_and_blocks {m : ℕ} (hm : 1 ≤ m)
    (hindex : Odd (unipotent m).index) (b : MulAut (Model m))
    (hU : (unipotent m).map b.toMonoidHom = unipotent m) :
    ∃ g : Model m, PreservesUnipotentPair m ((MulAut.conj g)⁻¹ * b) ∧
      PreservesSimpleBlocks m ((MulAut.conj g)⁻¹ * b) := by
  obtain ⟨g, hg⟩ := exists_inner_adjustment_preserving_pair hm b hU
  exact ⟨g, hg, preservesSimpleBlocks_of_pair hm hindex _ hg⟩

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
