module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Homology
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A vector test for the full homology kernel

Restrict the published column action to `homologyAction.ker`, and use the
literal vector v = (a - 1)e₀. Orbit–stabilizer counts this entire kernel,
including actors outside `localSubgroup`. The distinguished involution fixes
v, as it fixes every vector in ker(a - 1).

Twelve specified conjugates of the order-four local seed give 4096 candidate
images of v. These are actual words in the certified subgroup, with products
in increasing index order. They are only candidates: no coverage, distinctness,
or assertion that these words belong to the homology kernel is assumed.
Coverage of the full kernel orbit and the assertion that its point stabilizer
consists of 1 and a are separate premises of the counting lemmas below.

Source motivation: GLS3, Table 5.3i, printed p.270, gives the expected
2^(1+12).(3M22.2) centralizer structure, but supplies none of these premises.
The matrix and word provenance is recorded in `Model.Data` and
`TwoCoreCentralizer/source/README.md`. All vectors here use the published
first involution a and left column action, without a row-quotient comparison.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
namespace KernelBound

attribute [local irreducible] naturalAction

/-- The literal column `(a - 1)e₀`, considered as a fixed vector. -/
def baseVector : fixedVectors :=
  ⟨displacement (Pi.single 0 1), displacementVectors_le_fixedVectors ⟨_, rfl⟩⟩

instance kernelVectorAction : MulAction homologyAction.ker NaturalModule where
  smul c v := naturalAction (c : involutionCentralizer) v
  one_smul v := by change naturalAction 1 v = v; rw [map_one]; rfl
  mul_smul c d v := by
    change naturalAction ((c : involutionCentralizer) * d) v =
      naturalAction c (naturalAction d v)
    rw [map_mul]
    rfl

theorem kernel_smul (c : homologyAction.ker) (v : NaturalModule) :
    c • v = naturalAction (c : involutionCentralizer) v := rfl

def vectorOrbit : Set NaturalModule :=
  MulAction.orbit homologyAction.ker (baseVector : NaturalModule)

def vectorStabilizer : Subgroup homologyAction.ker :=
  MulAction.stabilizer homologyAction.ker (baseVector : NaturalModule)

theorem mem_vectorStabilizer_iff (c : homologyAction.ker) :
    c ∈ vectorStabilizer ↔
      naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) = baseVector :=
  Iff.rfl

theorem card_kernel_eq_orbit_mul_stabilizer :
    Nat.card homologyAction.ker = Nat.card vectorOrbit * Nat.card vectorStabilizer := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup homologyAction.ker
      (baseVector : NaturalModule))).symm

/-- The already certified central involution, in the full homology kernel. -/
def kernelInvolution : homologyAction.ker :=
  ⟨centralInvolution, centralInvolution_mem_homologyAction_ker⟩

theorem centralInvolution_fixes (v : fixedVectors) :
    naturalAction centralInvolution (v : NaturalModule) = v := by
  have he := LinearMap.congr_fun fixedAction_centralInvolution v
  exact congrArg Subtype.val he

theorem kernelInvolution_mem_vectorStabilizer : kernelInvolution ∈ vectorStabilizer :=
  centralInvolution_fixes baseVector

theorem vectorStabilizer_card_le_of_fixers
    (hfix : ∀ c : homologyAction.ker,
      naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) = baseVector →
        (c : involutionCentralizer) = 1 ∨ (c : involutionCentralizer) = centralInvolution) :
    Nat.card vectorStabilizer ≤ 2 := by
  classical
  let f : vectorStabilizer → Bool := fun c => decide ((c : homologyAction.ker) = 1)
  have hf : Function.Injective f := by
    intro c d he
    have hc := hfix c c.property
    have hd := hfix d d.property
    have hc' : (c : homologyAction.ker) = 1 ∨ (c : homologyAction.ker) = kernelInvolution :=
      hc.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    have hd' : (d : homologyAction.ker) = 1 ∨ (d : homologyAction.ker) = kernelInvolution :=
      hd.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    have he' : ((c : homologyAction.ker) = 1) ↔ ((d : homologyAction.ker) = 1) :=
      by simpa only [f, decide_eq_decide] using he
    apply Subtype.ext
    rcases hc' with hc' | hc'
    · exact hc'.trans (he'.mp hc').symm
    · rcases hd' with hd' | hd'
      · exact (he'.mpr hd').trans hd'.symm
      · exact hc'.trans hd'.symm
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_injective f hf


/-- Twelve seed conjugators, with `true` denoting X and `false` denoting Y. -/
def conjugatingWords : Vector (List Bool) 12 :=
  ⟨#[[],
    [false],
    [false, false],
    [false, false, true],
    [false, false, true, false],
    [false, false, true, false, true],
    [false, false, true, false, false],
    [false, false, true, false, true, false],
    [false, false, true, false, false, true],
    [false, false, true, false, true, false, true],
    [false, false, true, false, true, false, false],
    [false, false, true, false, false, true, false]], rfl⟩

/-- Every fixture is evaluated inside the certified local subgroup. -/
def conjugatingElement (i : Fin 12) : localSubgroup :=
  ((conjugatingWords.get i).map (fun b => if b then subgroupX else subgroupY)).prod

def orbitGenerator (i : Fin 12) : localSubgroup :=
  (conjugatingElement i)⁻¹ * localSeed * conjugatingElement i

abbrev OrbitMask := Fin 12 → Bool

def orbitRepresentative (m : OrbitMask) : localSubgroup :=
  (List.ofFn (fun i => if m i then orbitGenerator i else 1)).prod

def representativeVector (m : OrbitMask) : NaturalModule :=
  naturalAction (orbitRepresentative m : involutionCentralizer) (baseVector : NaturalModule)

theorem card_orbitMask : Nat.card OrbitMask = 4096 := by
  simp [OrbitMask, Nat.card_eq_fintype_card]

theorem vectorOrbit_card_le_of_cover
    (hcover : ∀ c : homologyAction.ker, ∃ m : OrbitMask,
      naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) =
        representativeVector m) :
    Nat.card vectorOrbit ≤ 4096 := by
  have hsub : vectorOrbit ⊆ Set.range representativeVector := by
    rintro v ⟨c, rfl⟩
    obtain ⟨m, hm⟩ := hcover c
    exact ⟨m, hm.symm⟩
  calc
    Nat.card vectorOrbit ≤ Nat.card (Set.range representativeVector) :=
      Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card OrbitMask := Nat.card_le_card_of_surjective _
      (Set.rangeFactorization_surjective (f := representativeVector))
    _ = 4096 := card_orbitMask

end KernelBound
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
