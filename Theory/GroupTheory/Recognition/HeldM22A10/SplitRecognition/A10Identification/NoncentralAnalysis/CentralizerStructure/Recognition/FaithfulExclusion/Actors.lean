module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Lift

/-!+# The actors needed for Held's faithful-action argument

The choices of lambda and xi may each be changed by the central involution
pi. `Actors` records only the resulting local geometry used on pp.234--235:
the eight words in the centralizer of pi*mu in A, the order-three actors'
required actions, and their membership in the canonical derived lift.
Its construction is a separate obligation. In particular it contains no
faithfulness, automorphism-group identification, or A6 conclusion.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.13 and 4.1--4.2.
The conjugation convention in the source is x^g = g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
namespace FaithfulExclusion

public abbrev Bit := Fin 2
public abbrev WordCode := Bit × Bit × Bit

@[expose] public def normalizedLam (b : Bit) : Coordinates.H :=
  Coordinates.pi ^ b.val * Coordinates.lam

@[expose] public def normalizedXi (d : Bit) : Coordinates.H :=
  Coordinates.pi ^ d.val * Coordinates.xi

@[expose] public def corePi : Coordinates.H := Coordinates.pi * Coordinates.mu

@[expose] public def coreTau (b : Bit) : Coordinates.H :=
  Coordinates.tau * normalizedLam b

@[expose] public def coreSwap (d : Bit) : Coordinates.H :=
  Coordinates.mup * normalizedXi d

/-- The eight words in Held's dihedral centralizer inside A. -/
@[expose] public def coreWord (b d : Bit) (i : WordCode) : Coordinates.H :=
  corePi ^ i.1.val * coreTau b ^ i.2.1.val * coreSwap d ^ i.2.2.val

universe u
variable {G : Type u} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}

/-- A as an actual subgroup of G; its normality is relative to C. -/
@[expose] public noncomputable def ambientCore (c : QuotientCore D e) : Subgroup G :=
  c.derivedLift.map (C D e).subtype

/-- The precise intermediate geometry used to prove faithfulness.
Existence is not asserted by this definition. -/
public structure Actors (c : QuotientCore D e) where
  lamChoice : Bit
  xiChoice : Bit
  nu : G
  alpha : G
  pi_mem : D.a10ModelEmbedding e corePi ∈ ambientCore c
  tau_mem : D.a10ModelEmbedding e (coreTau lamChoice) ∈ ambientCore c
  swap_mem : D.a10ModelEmbedding e (coreSwap xiChoice) ∈ ambientCore c
  nu_mem : nu ∈ ambientCore c
  beta_mem : D.a10ModelEmbedding e Coordinates.taup * alpha *
    D.a10ModelEmbedding e Coordinates.taup ∈ ambientCore c
  centralizer_words : ∀ y ∈ ambientCore c,
    Commute y (D.a10ModelEmbedding e corePi) →
    ∃ i : WordCode, y = D.a10ModelEmbedding e (coreWord lamChoice xiChoice i)
  nu_xi : Commute nu (D.a10ModelEmbedding e (normalizedXi xiChoice))
  pi_nu : nu⁻¹ * D.a10ModelEmbedding e corePi * nu =
    D.a10ModelEmbedding e (corePi * coreTau lamChoice)
  xi_alpha : alpha⁻¹ * D.a10ModelEmbedding e (normalizedXi xiChoice) * alpha =
    D.a10ModelEmbedding e Coordinates.mu
  pi_alpha : alpha⁻¹ * D.a10ModelEmbedding e Coordinates.pi * alpha =
    D.a10ModelEmbedding e (Coordinates.pi * normalizedXi xiChoice)

end FaithfulExclusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
