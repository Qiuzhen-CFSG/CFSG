module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent

/-!
# Extending the exact graph action from the integral generators

The Peirce inverse-transpose convention is a homomorphism. Simultaneous subgroup
closure induction extends integral conjugation and its literal quotient formula
from the two Eisenstein generators. Applied through the published matrix-cover
equivalence, this supplies every normalization and quotient field of
`LatticeGraph`; the integral swap, its square and scalar commutation are inputs.

Source: Aschbacher, Sporadic Groups (1994), proof of 49.5, p.283.
The matrix carrier and central quotient are exactly those of `Lattice.Block`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Conway Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph

variable {K : Type*} [Field K] [CharP K 2]

def twistHom : SL(3,K) →* SL(3,K) where
  toFun := graphTwist
  map_one' := by
    simp only [graphTwist, inv_one]
    have ht : (1 : SL(3,K)).transpose = 1 := Subtype.ext Matrix.transpose_one
    rw [ht, mul_one, graphFlip_square]
  map_mul' A B := by
    have ht : (B⁻¹ * A⁻¹).transpose = A⁻¹.transpose * B⁻¹.transpose :=
      Subtype.ext (Matrix.transpose_mul _ _)
    simp only [graphTwist, _root_.mul_inv_rev, ht]
    calc
      _ = graphFlip * A⁻¹.transpose * (graphFlip * graphFlip) *
          B⁻¹.transpose * graphFlip := by rw [graphFlip_square]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]

/-- The exact graph convention commutes with change of the coefficient field. -/
theorem twist_map {L : Type*} [Field L] [CharP L 2] (f : K →+* L) (A : SL(3,K)) :
    SpecialLinearGroup.map f (graphTwist A) = graphTwist (SpecialLinearGroup.map f A) := by
  have hf : SpecialLinearGroup.map f (graphFlip (K := K)) = graphFlip (K := L) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [graphFlip, SpecialLinearGroup.map]
  have ht (B : SL(3,K)) : SpecialLinearGroup.map f B.transpose =
      (SpecialLinearGroup.map f B).transpose := rfl
  simp only [graphTwist, map_mul, hf, ht, map_inv]

open Block

/-- The literal graph relation and integral normalization extend from the two
source generators to the entire concrete matrix group. -/
theorem extend_generators (s : LeechIsometryGroup) (u v : matrixGroup)
    (hA : s * matrixToLeech matrixGeneratorA * s⁻¹ = matrixToLeech u)
    (hB : s * matrixToLeech matrixGeneratorB * s⁻¹ = matrixToLeech v)
    (qA : matrixQuotient u = graphTwist (matrixQuotient matrixGeneratorA))
    (qB : matrixQuotient v = graphTwist (matrixQuotient matrixGeneratorB))
    (g : matrixGroup) :
    ∃ h : matrixGroup, s * matrixToLeech g * s⁻¹ = matrixToLeech h ∧
      matrixQuotient h = graphTwist (matrixQuotient g) := by
  let n : matrixGroup →* LeechIsometryGroup := (MulAut.conj s).toMonoidHom.comp matrixToLeech
  let t : matrixGroup →* SL(3,F) := twistHom.comp matrixQuotient
  change ∃ h, n g = matrixToLeech h ∧ matrixQuotient h = t g
  obtain ⟨g,hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨u,hA,qA⟩
    · exact ⟨v,hB,qB⟩
  | one =>
    refine ⟨1, ?_, ?_⟩
    · change n 1 = matrixToLeech 1
      rw [map_one, map_one]
    · change matrixQuotient 1 = t 1
      rw [map_one, map_one]
  | mul x y hx hy ihx ihy =>
    obtain ⟨a,ha,qa⟩ := ihx
    obtain ⟨b,hb,qb⟩ := ihy
    refine ⟨a*b, ?_, ?_⟩
    · change n (⟨x,hx⟩ * ⟨y,hy⟩) = _
      rw [map_mul, ha, hb, map_mul]
    · change _ = t (⟨x,hx⟩ * ⟨y,hy⟩)
      rw [map_mul, map_mul, qa, qb]
  | inv x hx ih =>
    obtain ⟨a,ha,qa⟩ := ih
    refine ⟨a⁻¹, ?_, ?_⟩
    · change n (⟨x,hx⟩ : matrixGroup)⁻¹ = _
      rw [map_inv, ha, map_inv]
    · change _ = t (⟨x,hx⟩ : matrixGroup)⁻¹
      rw [map_inv, map_inv, qa]

/-- Two checked generator identities supply the exact cover and quotient fields
of `LatticeGraph`; square and marked scalar commutation remain explicit. -/
def ofGenerators (s : LeechIsometryGroup)
    (hs : s*s ∈ leechCentralSigns)
    (hc : ∀ a, Commute (scalarFive (latticeBlock.marking a)) (leechCentralProjection s))
    (u v : matrixGroup)
    (hA : s * matrixToLeech matrixGeneratorA * s⁻¹ = matrixToLeech u)
    (hB : s * matrixToLeech matrixGeneratorB * s⁻¹ = matrixToLeech v)
    (qA : matrixQuotient u = graphTwist (matrixQuotient matrixGeneratorA))
    (qB : matrixQuotient v = graphTwist (matrixQuotient matrixGeneratorB)) :
    LatticeGraph latticeBlock where
  swap := s
  square := hs
  commute := hc
  normalizes g := by
    obtain ⟨x,rfl⟩ := matrixCoverEquiv.surjective g
    obtain ⟨y,hy,_⟩ := extend_generators s u v hA hB qA qB x
    exact ⟨y,hy.symm⟩
  twist g := by
    obtain ⟨x,rfl⟩ := matrixCoverEquiv.surjective g
    obtain ⟨y,hy,qy⟩ := extend_generators s u v hA hB qA qB x
    have he : (⟨s * (matrixCoverEquiv x).val * s⁻¹, ⟨y,hy.symm⟩⟩ : latticeBlock.cover) =
        matrixCoverEquiv y := Subtype.ext hy
    rw [he, latticeBlock_quotient, latticeBlock_quotient, qy]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
