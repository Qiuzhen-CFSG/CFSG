module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.DerivedApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.DerivedRoots

/-!
# Original U₅ root-center coordinates and their crossing equations

Starting with the original linear epimorphism and projective unitary panel
marking, construct the Hermitian coordinates of the actual linear-derived
subgroup. Its diagonal lines are exactly the intrinsic centers of the two
whole nonabelian unitary roots; its off-diagonal plane is the actual
crossed linear root. All containments, cardinalities and coordinate
identifications used here are derived from the source profile.

The tensor action gives the trace crossing and the crossing with an entire
central root element, as equalities in the same quotient. The chosen linear
reflection exchanges the two centers and conjugates the off-diagonal
parameter. The original consumer spells out both product laws using Q.q.
The parameter field is the field selected by Hermitian recognition, and
all positive binary degrees, including q = 2 and q = 4, are retained.

These are the center part of the U₅ equations. B and D below parameterize
root centers, not the whole nonabelian roots. Their synchronization with
the SU₃ parameters and the remaining full-root, Cartan and Weyl equations
are still needed before FiveData can be constructed.
Source: Fong--Seitz II (8C), printed pp.206--207 (PDF pp.16--17),
(8.21)--(8.23), (8.30), with right conjugation converted explicitly.
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open Representation.OrthogonalFourMinus.FiniteModel
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Theory.PSL2.SemilinearCoverage
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)

include h hK hE hfixed hJ hm hij hVi hVj s hf hk ν

/-- The actual source profile constructs all three derived-root coordinates,
the two polynomial crossings, and the specified linear reflection action. -/
theorem marked_derived_root_relations :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q mark h split i hVi f hf hk
    ∃ (ξ : K ≃+* Field n)
      (e : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))),
      let l := fieldRelabelledActor Q split i hVi μ₀ s n ξ
      let v := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
        Subgroup (X ⧸ Q.D)).subtype.comp e.toMonoidHom
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      (∀ (g : SL(2,Field n)) (p : Space n),
        l g * (e (.ofAdd p) : X ⧸ Q.D) * (l g)⁻¹ = e (.ofAdd (action n g p))) ∧
      r.A.range = simpleRoot Q split i ∧
      r.B.range = (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype ∧
      r.C.range = rootAt Q split i (Q.simple j) ∧
      r.D.range = (center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype ∧
      FourPositive.Relations (Field n) (conjugation n) (conjugation_involutive n) r ∧
      (∀ b : fixedField n, (s.val : X ⧸ Q.D) * r.B (.ofAdd b) * s.val = r.D (.ofAdd b)) ∧
      (∀ c : Field n, (s.val : X ⧸ Q.D) * r.C (.ofAdd c) * s.val =
        r.C (.ofAdd (conjugation n c))) ∧
      ∀ x ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆,
        ∃ (d : fixedField n) (c : Field n) (b : fixedField n),
          x = r.D (.ofAdd d) * r.C (.ofAdd c) * r.B (.ofAdd b) := by
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q mark h split i hVi f hf hk
  obtain ⟨ξ,e,he⟩ := marked_aligned_derived_realization Q split mark h J n
    hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν
  let l := fieldRelabelledActor Q split i hVi μ₀ s n ξ
  let v := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
    Subgroup (X ⧸ Q.D)).subtype.comp e.toMonoidHom
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  have hA := fieldRelabelledActor_root_range Q split i hVi μ₀ s n ξ
  have hs := fieldRelabelledActor_weyl Q split i hVi μ₀ s n ξ
  change l (weyl (Field n)) = (s.val : X ⧸ Q.D) at hs
  obtain ⟨hBcenter,hsmall⟩ := simpleRoot_derived_center_card Q split j hVj J
    (NeZero.pos n) hE hfixed hJ ν
  have hZ := (unitary_simpleRoot_special Q split J (NeZero.pos n) hE hfixed hJ j hVj ν).2
  have hDcenter := crossed_derived_center_eq Q split i j s hZ
  have hcross : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≤
      ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ := by
    rw [hDcenter]
    exact cross_root_commutator_le_center Q split hm i j hij hVi hVj
  have hcomm := unitary_opposite_commutator Q split J (NeZero.pos n) hK hE hfixed hJ
    hm i j hij hVi hVj s (GTwoSource.alignedPinning Q split i hVi μ₀ s).symm ν
  have hC : rootAt Q split i (Q.simple j) ≤
      ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
    rw [←hcomm]
    exact commutator_mono (opposite_roots_le_remainder Q split j i hij.symm).1
      (opposite_roots_le_remainder Q split j i hij.symm).2
  have hlarge : Nat.card (simpleRoot Q split i) = Nat.card (Field n) :=
    (GTwoSource.simpleRoot_card Q split i hVi μ₀).trans (Nat.card_congr ξ.toEquiv)
  refine ⟨ξ,e,he,hA,?_,?_,?_,FourTensor.relations _ _ _ l v he,?_,?_,?_⟩
  · exact (derived_B_range Q split n i j hij hm hVi hVj s l e he hA hs hsmall).trans hBcenter
  · exact derived_C_range Q split n i j hij hm hVi hVj s l e he hA hs hsmall hcross hC hlarge
  · exact (derived_D_range Q split n i j hij hm hVi hVj s l e he hA hsmall).trans hDcenter
  · intro b
    simpa only [hs] using FourCartan.weyl_B (Field n) (conjugation n)
      (conjugation_involutive n) l v he b
  · intro c
    simpa only [hs] using FourCartan.weyl_C (Field n) (conjugation n)
      (conjugation_involutive n) l v he c
  · intro x hx
    let p := (e.symm ⟨x,hx⟩).toAdd
    obtain ⟨d,c,b,hp⟩ := FourTensor.core_decomposition (Field n) (conjugation n)
      (conjugation_involutive n) p
    refine ⟨d,c,b,?_⟩
    have hv : v (.ofAdd p) = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
    rw [←hv,hp]
    change v ((.ofAdd (FourTensor.diagonalTop (Field n) (conjugation n)
      (conjugation_involutive n) d) * .ofAdd (FourTensor.offDiagonal (Field n)
        (conjugation n) (conjugation_involutive n) c)) *
          .ofAdd (FourTensor.diagonalBottom (Field n) (conjugation n)
            (conjugation_involutive n) b)) = _
    rw [map_mul,map_mul]
    rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
variable {G K E : Type*} [Group G]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)

include h hK hE hfixed hJ hm hij hVi hVj s hf hk ν

/-- Both derived-layer polynomial laws hold on literal original Q.q products.
The same constructed maps fill the two entire root centers and the crossed
linear root; no matching-label or crossing premise is supplied. -/
theorem original_derived_root_equations :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (ξ : K ≃+* Field n)
      (e : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
          Subgroup ((generated L S) ⧸ Q.D))),
      let l := fieldRelabelledActor Q split i hVi μ₀ s n ξ
      let v := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
        Subgroup ((generated L S) ⧸ Q.D)).subtype.comp e.toMonoidHom
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      (∀ (g : SL(2,Field n)) (p : Space n),
        l g * (e (.ofAdd p) : (generated L S) ⧸ Q.D) * (l g)⁻¹ = e (.ofAdd (action n g p))) ∧
      r.A.range = simpleRoot Q split i ∧
      r.B.range = (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype ∧
      r.C.range = rootAt Q split i (Q.simple j) ∧
      r.D.range = (center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype ∧
      FourPositive.Relations (Field n) (conjugation n) (conjugation_involutive n) r ∧
      (∀ (a c : Field n) (A C : generated L S)
        (_hA : Q.q A = r.A (.ofAdd a)) (_hC : Q.q C = r.C (.ofAdd c)),
        Q.q (C*A) = Q.q A *
          r.D (.ofAdd (FourPositive.traceParameter (Field n) (conjugation n)
            (conjugation_involutive n) a c)) * Q.q C) ∧
      (∀ (a : Field n) (b : fixedField n) (A B : generated L S)
        (_hA : Q.q A = r.A (.ofAdd a)) (_hB : Q.q B = r.B (.ofAdd b)),
        Q.q (B*A) = Q.q A *
          r.D (.ofAdd (FourPositive.normParameter (Field n) (conjugation n)
            (conjugation_involutive n) a b)) * r.C (.ofAdd (a*(b : Field n))) * Q.q B) ∧
      ∀ x : generated L S, Q.q x ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ →
        ∃ (d : fixedField n) (c : Field n) (b : fixedField n),
          Q.q x = r.D (.ofAdd d) * r.C (.ofAdd c) * r.B (.ofAdd b) := by
  dsimp only
  obtain ⟨ξ,e,he,hA,hB,hC,hD,hr,_,_,hcollect⟩ := marked_derived_root_relations
    Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν
  refine ⟨ξ,e,he,hA,hB,hC,hD,hr,?_,?_,fun x hx => hcollect (Q.q x) hx⟩
  · intro a c A C hA hC
    rw [map_mul,hA,hC]
    exact hr.CA a c
  · intro a b A B hA hB
    rw [map_mul,hA,hB]
    exact hr.BA a b

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
