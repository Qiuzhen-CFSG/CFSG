module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter1.Defs
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PGroup.OmegaAmbient


/-!
# The marked subgroups in Section 12.8

These are the literal constructions in Aschbacher–Smith, combined manuscript
of 1 March 2004, Hypothesis 12.8.1(2) and Notation 12.8.2, printed pp.849–852.
`RankTwoHypothesis` records the second source alternative, including the
actual ambient Sylow subgroup, proper-K input, relative normality, unique
maximal two-local overgroup and quotient isomorphism. Its class parameter
must be instantiated with the full known-simple class in the final assembly.
The higher-rank alternative and the construction of the invariant flag are
separate source obligations; an `InvariantFlag` is only a marking of a flag.

All local subgroups are embedded in the same ambient group. Conjugation is
right conjugation, `A^g = g⁻¹ A g`. The exceptional `L₂,L₃` for `n=5` use
the solvable residual; the other `Lᵢ` use the two-residual. `P` is the flag
stabilizer inside `LT` obtained by omitting the point; identifying it as the
minimal parabolic acting on `V₂` still requires the natural-action proof.
`I₂` is its span of `U`, not a marked maximal parabolic.
No action, core, normalizer-product or recognition conclusion is assumed.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section08

universe u
variable {G : Type u} [Group G]

/-- Right conjugation, as in the source. -/
def conjugate (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

/-- The intrinsic center, included into the ambient group. -/
def centerIn (A : Subgroup G) : Subgroup G := (center A).map A.subtype

/-- The source subgroup `Z = Ω₁(Z(T))`. -/
def sylowOmega (T : Sylow 2 G) : Subgroup G :=
  omegaOneAmbient (centerIn (T : Subgroup G))

/-- The actual seed `V = ⟨Zᴹ⟩` in the rank-two source alternative. -/
def rankTwoSeed (T : Sylow 2 G) (M : Subgroup G) : Subgroup G :=
  conjugateSpanBy (sylowOmega T) M

/-- The relative normalizer `M_V = N_M(V)`. -/
def seedNormalizer (M V : Subgroup G) : Subgroup G := M ⊓ normalizer (V : Set G)

/-- The local two-core `Q_H`, embedded into `G`. -/
def QH (J : Subgroup G) : Subgroup G := J.pCoreIn 2

/-- The literal quotient `H* = H/O₂(H)`. -/
abbrev HStar (J : Subgroup G) := J ⧸ pCore 2 J

/-- Exactly alternative (2) of Hypothesis 12.8.1. Rank is the source two-rank;
elementary abelianness is a deduction, not an additional premise. -/
structure RankTwoHypothesis (K : GroupClass.{u}) [Finite G]
    (T : Sylow 2 G) (L M : Subgroup G) : Prop where
  simpleQTKE : IsSimpleQTKE K G
  maximal : IsMaximalTwoLocal M
  sylow_le : (T : Subgroup G) ≤ M
  rank : primeRank 2 (rankTwoSeed T M) = 2
  L_le : L ≤ M
  L_normal : (L.subgroupOf M).Normal
  L_residual : pResidual 2 L = ⊤
  unique : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} = {M}
  centralizer : (L ⊔ (T : Subgroup G)) ⊓ centralizer (rankTwoSeed T M : Set G) =
    (L ⊔ (T : Subgroup G)).pCoreIn 2
  quotient_model : Nonempty
    (((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      Equiv.Perm (Fin 3))
  escape : ¬ Subgroup.centralizer (sylowOmega T : Set G) ≤ M

/-- A marked complete binary flag in the actual subgroup `V`, invariant under
the fixed ambient Sylow subgroup. Existence follows from the natural action. -/
structure InvariantFlag (T : Sylow 2 G) (V : Subgroup G) (n : ℕ) where
  Vi : ℕ → Subgroup G
  le_seed : ∀ i, Vi i ≤ V
  monotone : Monotone Vi
  card : ∀ i, i ≤ n → Nat.card (Vi i) = 2 ^ i
  last : Vi n = V
  invariant : ∀ i, (T : Subgroup G) ≤ normalizer (Vi i : Set G)

namespace InvariantFlag
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

def Gi (F : InvariantFlag T V n) (i : ℕ) : Subgroup G := normalizer (F.Vi i : Set G)

def Mi (F : InvariantFlag T V n) (M : Subgroup G) (i : ℕ) : Subgroup G := M ⊓ F.Gi i

def Li (F : InvariantFlag T V n) (L : Subgroup G) (i : ℕ) : Subgroup G :=
  let N := L ⊓ F.Gi i
  if n = 5 ∧ (i = 2 ∨ i = 3) then (solvableResidual N).map N.subtype
  else (pResidual 2 N).map N.subtype

def Ri (F : InvariantFlag T V n) (L : Subgroup G) (i : ℕ) : Subgroup G :=
  (F.Li L i ⊔ (T : Subgroup G)).pCoreIn 2

def Hz (F : InvariantFlag T V n) (L M : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Chapter1.HOver G (F.Li L 1 ⊔ (T : Subgroup G) : Set G) ∧
    J ≤ F.Gi 1 ∧ ¬ J ≤ M}

def UH (_F : InvariantFlag T V n) (J : Subgroup G) : Subgroup G := conjugateSpanBy V J

def H (F : InvariantFlag T V n) : Subgroup G := F.Gi 1

def U (F : InvariantFlag T V n) : Subgroup G := F.UH F.H

def W (F : InvariantFlag T V n) : Subgroup G := F.U ⊓ centralizer (F.Vi 2 : Set G)

def X (F : InvariantFlag T V n) (g : G) : Subgroup G := conjugate F.W g

def E (F : InvariantFlag T V n) (g : G) : Subgroup G := F.W ⊓ F.X g

/-- The flag stabilizer with the point omitted; for `n=2` this is all of `LT`. -/
def P (F : InvariantFlag T V n) (L : Subgroup G) : Subgroup G :=
  (L ⊔ (T : Subgroup G)) ⊓ ⨅ i : ℕ, ⨅ (_ : 2 ≤ i ∧ i < n), F.Gi i

def I₂ (F : InvariantFlag T V n) (L : Subgroup G) : Subgroup G :=
  conjugateSpanBy F.U (F.P L)

def ZU (F : InvariantFlag T V n) : Subgroup G := centerIn F.U

abbrev Uhat (F : InvariantFlag T V n) := F.U ⧸ center F.U

/-- The point subgroup is normal in its actual normalizer. -/
instance point_normal (F : InvariantFlag T V n) : ((F.Vi 1).subgroupOf F.H).Normal := by
  change ((F.Vi 1).subgroupOf (normalizer (F.Vi 1 : Set G))).Normal
  infer_instance

/-- The ambient quotient for all tilded subgroups. -/
abbrev G₁tilde (F : InvariantFlag T V n) := F.H ⧸ (F.Vi 1).subgroupOf F.H

/-- The literal image in `G₁/V₁`; containment in `G₁` is supplied when used. -/
def tilde (F : InvariantFlag T V n) (A : Subgroup G) : Subgroup F.G₁tilde :=
  (A.subgroupOf F.H).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))

end InvariantFlag
end CFSG.Quasithin.Chapter12.Section08
