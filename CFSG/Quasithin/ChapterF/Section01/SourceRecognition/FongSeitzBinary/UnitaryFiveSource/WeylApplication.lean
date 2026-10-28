module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.CartanApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.MarkedReflection

/-!
# Both marked reflections on the original U₅ root groups

The natural source flag constructs the actual unitary Weyl lift in N.
Together with the supplied linear lift it satisfies the six whole-root
reflection equations. The unitary D equation includes its center; the
linear C equation retains the field involution. The supplied second lift
is recovered as a Cartan multiple of the constructed one. Original
applications use the literal Q.q and preserve both actor squares.
Source: Fong--Seitz II (8C), pp.203–210, through (8.37).
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative MonoidAlgebra
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {G X K E : Type*} [Group G] [Group X] [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2)
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (t : RootReflection Q split j)
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
  (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))



include e h hK hE hfixed hJ hconj hm hij hVi hVj s t hf hk ν hπ hπν hindexi hindexj hQi hderived hfrattini

/-- Construct both marked Weyl lifts and all six whole-root reflection
laws from the original synchronized source coordinates. -/
theorem marked_root_reflections :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (lifts : MarkedWeyl.Lifts Q j),
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      FivePositive.Relations (fiveForm J) r ∧
      (Function.Injective (chartWord Q r) ∧ Set.range (chartWord Q r) = (split.U : Set (X ⧸ Q.D)) ∧ r.generated = split.U) ∧
      lifts.s = s.val ∧
      (lifts.t : X ⧸ Q.D) = unitaryWeyl Q split j J hJ θ ∧
      (∃ u : Eˣ, (t.val : X ⧸ Q.D) = unitaryTorus Q split j J hJ θ u * lifts.t) ∧
      (lifts.s : X ⧸ Q.D)*lifts.s = 1 ∧
      (lifts.t : X ⧸ Q.D)*lifts.t = 1 ∧
      (∀ p, (lifts.s : X ⧸ Q.D)*r.B p*lifts.s = r.D p) ∧
      (∀ p, (lifts.s : X ⧸ Q.D)*r.D p*lifts.s = r.B p) ∧
      (∀ a, (lifts.s : X ⧸ Q.D)*r.C (.ofAdd a)*lifts.s = r.C (.ofAdd (J.conj a))) ∧
      (∀ a, (lifts.t : X ⧸ Q.D)*r.A (.ofAdd a)*lifts.t = r.C (.ofAdd a)) ∧
      (∀ a, (lifts.t : X ⧸ Q.D)*r.C (.ofAdd a)*lifts.t = r.A (.ofAdd a)) ∧
      ∀ p, (lifts.t : X ⧸ Q.D)*r.D p*lifts.t = r.D p := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c,ξ,k,hk0,hcover,hpanel,hb,hc,hA,hC,hD,hγ,hrel,hco,H,hH,hHmem,hHA,hHC,hHB,hHD⟩ :=
    marked_full_cartan_relations Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  let lifts := synchronizedWeylLifts Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA γ hC t
  have hs : lifts.s = s.val := rfl
  have ht : (lifts.t : X ⧸ Q.D) = unitaryWeyl Q split j J hJ θ :=
    synchronizedWeylLifts_t Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA γ hC t
  obtain ⟨hss,hsB,hsD⟩ := synchronizedRoots_linear_reflection Q split i j hVi s μ₀ J b ξ γ
  refine ⟨g,θ,b,γ,ξ,lifts,hcover,hpanel,hb,hrel,hco,hs,ht,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht]
    exact unitaryWeyl_source_factor Q split i j hij hVi hVj s μ₀ J hJ θ c hc ξ k hk0 hA γ hC t
  · simpa only [hs] using hss
  · simpa only [ht] using unitaryWeyl_square Q split j J hJ θ
  · simpa only [hs] using hsB
  · simpa only [hs] using hsD
  · intro a
    rw [hs]
    exact hγ a
  · intro a
    rw [ht]
    exact unitaryWeyl_A Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA γ hC t a
  · intro a
    rw [ht]
    exact unitaryWeyl_C Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA γ hC t a
  · intro p
    rw [ht]
    exact unitaryWeyl_D Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA γ hC t hm hrel p

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {G K E : Type*} [Group G] [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2)
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (t : RootReflection Q split j)
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
  (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))




include h hK hE hfixed hJ hconj hm hij hVi hVj s t hf hk ν hπ hπν hindexi hindexj hQi hderived hfrattini

/-- All six reflection formulas on literal original Q.q representatives,
retaining the whole nonabelian roots and their centers. -/
theorem original_root_reflections :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (lifts : MarkedWeyl.Lifts Q j),
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      lifts.s = s.val ∧
      (lifts.t : (generated L S) ⧸ Q.D) = unitaryWeyl Q split j J hJ θ ∧
      (∃ u : Eˣ, (t.val : (generated L S) ⧸ Q.D) = unitaryTorus Q split j J hJ θ u * lifts.t) ∧
      (∀ (p : hermitianUnipotentCoord J) (W B D : generated L S),
        Q.q W = lifts.s → Q.q B = r.B p → Q.q D = r.D p →
        Q.q (W*B*W) = r.D p ∧ Q.q (W*D*W) = r.B p) ∧
      (∀ (a : E) (W C : generated L S),
        Q.q W = lifts.s → Q.q C = r.C (.ofAdd a) →
        Q.q (W*C*W) = r.C (.ofAdd (J.conj a))) ∧
      (∀ (a : E) (W A C : generated L S),
        Q.q W = lifts.t → Q.q A = r.A (.ofAdd a) → Q.q C = r.C (.ofAdd a) →
        Q.q (W*A*W) = r.C (.ofAdd a) ∧ Q.q (W*C*W) = r.A (.ofAdd a)) ∧
      ∀ (p : hermitianUnipotentCoord J) (W D : generated L S),
        Q.q W = lifts.t → Q.q D = r.D p → Q.q (W*D*W) = r.D p := by
  dsimp only
  obtain ⟨g,θ,b,γ,ξ,lifts,hcover,hpanel,hb,hrel,hco,hs,ht,hfactor,hss,htt,hsB,hsD,hsC,htA,htC,htD⟩ :=
    marked_root_reflections Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,ξ,lifts,hcover,hpanel,hs,ht,hfactor,?_,?_,?_,?_⟩
  · intro p W B D hW hB hD
    simpa only [map_mul,hW,hB,hD] using And.intro (hsB p) (hsD p)
  · intro a W C hW hC
    simpa only [map_mul,hW,hC] using hsC a
  · intro a W A C hW hA hC
    simpa only [map_mul,hW,hA,hC] using And.intro (htA a) (htC a)
  · intro p W D hW hD
    simpa only [map_mul,hW,hD] using htD p

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
