module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Reduction
import Mathlib.Tactic.FinCases

/-!
# Kernel-checked point-orbit and stabilizer-transition witnesses

All 1600 point witnesses and all 864 stabilizer transitions are checked against
the existing packed ATLAS point maps by kernel reduction. The point witnesses
place every point in a displayed normalizer orbit. The transition identities,
together with the certified Schreier chain, cover the actual point-zero
stabilizer by the 144 displayed left cosets of the normalizer.

The finite checks are elaborated sequentially to bound memory. They use the
unchanged candidate tables and fixed representative conventions. No exact
normalizer order or disjointness of the displayed cosets is assumed.

Source: the primary ATLAS generators and the certified ambient Schreier chain;
see `Coverage/source/README.md` for provenance and reproduction.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
open Atlas1600OrderCertificate

-- Check one batch at a time to bound the live kernel reduction state.
set_option Elab.async false

set_option maxRecDepth 20000 in
private theorem points00 : ∀ p : Fin 64,
    pointTest ⟨0 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points01 : ∀ p : Fin 64,
    pointTest ⟨64 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points02 : ∀ p : Fin 64,
    pointTest ⟨128 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points03 : ∀ p : Fin 64,
    pointTest ⟨192 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points04 : ∀ p : Fin 64,
    pointTest ⟨256 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points05 : ∀ p : Fin 64,
    pointTest ⟨320 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points06 : ∀ p : Fin 64,
    pointTest ⟨384 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points07 : ∀ p : Fin 64,
    pointTest ⟨448 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points08 : ∀ p : Fin 64,
    pointTest ⟨512 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points09 : ∀ p : Fin 64,
    pointTest ⟨576 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points10 : ∀ p : Fin 64,
    pointTest ⟨640 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points11 : ∀ p : Fin 64,
    pointTest ⟨704 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points12 : ∀ p : Fin 64,
    pointTest ⟨768 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points13 : ∀ p : Fin 64,
    pointTest ⟨832 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points14 : ∀ p : Fin 64,
    pointTest ⟨896 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points15 : ∀ p : Fin 64,
    pointTest ⟨960 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points16 : ∀ p : Fin 64,
    pointTest ⟨1024 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points17 : ∀ p : Fin 64,
    pointTest ⟨1088 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points18 : ∀ p : Fin 64,
    pointTest ⟨1152 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points19 : ∀ p : Fin 64,
    pointTest ⟨1216 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points20 : ∀ p : Fin 64,
    pointTest ⟨1280 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points21 : ∀ p : Fin 64,
    pointTest ⟨1344 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points22 : ∀ p : Fin 64,
    pointTest ⟨1408 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points23 : ∀ p : Fin 64,
    pointTest ⟨1472 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem points24 : ∀ p : Fin 64,
    pointTest ⟨1536 + p.val, by omega⟩ = true := by
  apply allFin
  decide +kernel

private theorem pointsBatch (i : Fin 25) (j : Fin 64) :
    pointTest ⟨64 * i.val + j.val, by omega⟩ = true := by
  fin_cases i
  · exact points00 j
  · exact points01 j
  · exact points02 j
  · exact points03 j
  · exact points04 j
  · exact points05 j
  · exact points06 j
  · exact points07 j
  · exact points08 j
  · exact points09 j
  · exact points10 j
  · exact points11 j
  · exact points12 j
  · exact points13 j
  · exact points14 j
  · exact points15 j
  · exact points16 j
  · exact points17 j
  · exact points18 j
  · exact points19 j
  · exact points20 j
  · exact points21 j
  · exact points22 j
  · exact points23 j
  · exact points24 j

public theorem points_checked (p : Fin 1600) : pointTest p = true := by
  let i : Fin 25 := ⟨p.val / 64, by omega⟩
  let j : Fin 64 := ⟨p.val % 64, by omega⟩
  have he : p = ⟨64 * i.val + j.val, by omega⟩ := by
    apply Fin.ext
    dsimp [i, j]
    omega
  rw [he]
  exact pointsBatch i j

set_option maxRecDepth 20000 in
private theorem transitions0 : ∀ j : Fin 144, transitionTest 0 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem transitions1 : ∀ j : Fin 144, transitionTest 1 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem transitions2 : ∀ j : Fin 144, transitionTest 2 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem transitions3 : ∀ j : Fin 144, transitionTest 3 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem transitions4 : ∀ j : Fin 144, transitionTest 4 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem transitions5 : ∀ j : Fin 144, transitionTest 5 j = true := by
  apply allFin
  decide +kernel

public theorem transitions_checked (i : Fin 6) (j : Fin 144) : transitionTest i j = true := by
  fin_cases i
  · exact transitions0 j
  · exact transitions1 j
  · exact transitions2 j
  · exact transitions3 j
  · exact transitions4 j
  · exact transitions5 j

/-- Every point is reached by the displayed actual normalizer element from its
chosen orbit representative. -/
public theorem point_orbit (p : Fin 1600) :
    (normalWord (pointNormal p)).val ((orbitRep (pointOrbit p)).val 0) = p :=
  pointTest_sound p (points_checked p)

/-- The 32 displayed points cover the action of the actual thirteen-normalizer. -/
public theorem point_orbit_cover (p : Fin 1600) :
    ∃ (i : Fin 32) (n : thirteenNormalizer), n.val.val ((orbitRep i).val 0) = p :=
  ⟨pointOrbit p, normalizerElement (pointNormal p), point_orbit p⟩

/-- The actual point-zero stabilizer is covered by the 144 displayed left cosets
of the actual thirteen-normalizer. No exact normalizer order is required. -/
public theorem stabilizer_cover (x : Atlas1600Group) (hx : x.val 0 = 0) :
    ∃ (j : Fin 144) (n : thirteenNormalizer), x = stabilizerRep j * n.val :=
  stabilizer_cover_of_transitions transitions_checked x hx

end Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
