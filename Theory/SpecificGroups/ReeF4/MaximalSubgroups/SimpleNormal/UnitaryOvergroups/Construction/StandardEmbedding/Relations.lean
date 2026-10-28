module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.StandardEmbedding.Generators
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Independent unitary and Ree word calculations

The explicit rank-one relations use the full diagonal torus and the two
Bruhat forms. `UnitaryPresentation` asks for their completeness for the
actual projective unitary matrices. `ReeRealizations` separately asks for
fixed split-F4 matrices satisfying those relations and separating the
identity in the two forms. Neither obligation is asserted here.

The assembly in `StandardEmbedding` descends word evaluation through the
matrix presentation and proves injectivity using Bruhat separation. Thus
the two calculations can be proved independently, and neither takes a
projective embedding as an input.

Source: Malle, J. Algebra 139 (1991), 52–69, Section 2.5, manuscript pp.10–11,
DOI 10.1016/0021-8693(91)90283-E. His root-word formula and extra cyclic
normalizer supply the Ree-side construction. The displayed projective
Bruhat relation uses the scalar factor `b / bar b` at the matrix level.
-/

@[expose] public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Construction.StandardEmbedding

/-- The rank-one relations for the full projective unitary group. -/
inductive Relator (m : ℕ) : Word m → Prop where
  | root_zero : Relator m (rootWord (RootParameter.zero m))
  | root_mul (p q : RootParameter m) :
      Relator m (rootWord p * rootWord q * (rootWord (p.mul q))⁻¹)
  | torus_one : Relator m (torusWord 1)
  | torus_mul (t s : (E m)ˣ) :
      Relator m (torusWord t * torusWord s * (torusWord (t * s))⁻¹)
  | torus_root (t : (E m)ˣ) (p : RootParameter m) :
      Relator m (torusWord t * rootWord p * (torusWord t)⁻¹ *
        (rootWord (p.scale t))⁻¹)
  | weyl_sq : Relator m (weylWord m * weylWord m)
  | weyl_torus (t : (E m)ˣ) :
      Relator m (weylWord m * torusWord t * weylWord m *
        (torusWord (conjugateInverse t))⁻¹)
  | bruhat (p : RootParameter m) (hb : p.b ≠ 0) :
      Relator m (weylWord m * rootWord p * weylWord m *
        (rootWord (p.bruhatLeft hb) * torusWord (bruhatTorus p hb) *
          weylWord m * rootWord (p.bruhatRight hb))⁻¹)

/-- Relations are imposed by their normal closure in the free group. -/
def relationSubgroup (m : ℕ) : Subgroup (Word m) := Subgroup.normalClosure {w | Relator m w}

inductive NormalForm (m : ℕ) where
  | small (p : RootParameter m) (t : (E m)ˣ)
  | big (p : RootParameter m) (t : (E m)ˣ) (q : RootParameter m)

def normalWord {m : ℕ} : NormalForm m → Word m
  | .small p t => rootWord p * torusWord t
  | .big p t q => rootWord p * torusWord t * weylWord m * rootWord q

/-- The classical matrix calculation: generation, the exact presentation
kernel, and reduction to the two Bruhat forms. These are proof obligations. -/
def UnitaryPresentation : Prop :=
  ∀ m, 1 ≤ m → Function.Surjective (unitaryEval m) ∧
    (unitaryEval m).ker = relationSubgroup m ∧
    ∀ w : Word m, ∃ n : NormalForm m,
      w * (normalWord n)⁻¹ ∈ relationSubgroup m

/-- Concrete candidate images in the root-generated split F4 matrix group.
This structure has no homomorphism, fixedness, or injectivity field. -/
structure ReeGeneratorData (m : ℕ) where
  rootImage : RootParameter m → SplitGroup m
  torusImage : (E m)ˣ → SplitGroup m
  weylImage : SplitGroup m

def ReeGeneratorData.generator {m : ℕ} (d : ReeGeneratorData m) :
    Generator m → SplitGroup m
  | .root p => d.rootImage p
  | .torus t => d.torusImage t
  | .weyl => d.weylImage

def ReeGeneratorData.eval {m : ℕ} (d : ReeGeneratorData m) : Word m →* SplitGroup m :=
  FreeGroup.lift d.generator

def ReeGeneratorData.Fixed {m : ℕ} (d : ReeGeneratorData m) : Prop :=
  ∀ g : Generator m, reeTwist m (d.generator g) = d.generator g

def ReeGeneratorData.Relations {m : ℕ} (d : ReeGeneratorData m) : Prop :=
  ∀ w : Word m, Relator m w → d.eval w = 1

/-- Only separation at the identity is needed, in the two normal forms. -/
def ReeGeneratorData.Separated {m : ℕ} (d : ReeGeneratorData m) : Prop :=
  (∀ p t, d.rootImage p * d.torusImage t = 1 → p.a = 0 ∧ p.b = 0 ∧ t = 1) ∧
  (∀ p t q, d.rootImage p * d.torusImage t * d.weylImage * d.rootImage q ≠ 1)

/-- The independent Ree root-matrix construction. It does not assume the
unitary presentation or give an already descended projective embedding. -/
def ReeRealizations : Prop :=
  ∀ m, 1 ≤ m → ∃ d : ReeGeneratorData m, d.Fixed ∧ d.Relations ∧ d.Separated

end ReeF4.MaximalSubgroups.SimpleNormal.Construction.StandardEmbedding
