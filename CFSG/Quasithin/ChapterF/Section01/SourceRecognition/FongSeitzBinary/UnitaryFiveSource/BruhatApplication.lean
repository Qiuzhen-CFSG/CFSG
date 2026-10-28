module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.CartanApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.RankOneBruhat

/-!
# Original U₅ rank-one Bruhat formulas

The full-Cartan source constructor supplies one common set of roots,
field labels and torus. The aligned linear reflection and the actual SU₃
Weyl image satisfy both exact rank-one Bruhat formulas on these data.
The full B,D swap and C-conjugation equations for the linear reflection
are retained. The original application spells out the same Q.q words and
preserves the covering map and projective panel square, including q=2,4.

The SU₃ Weyl image is not yet packaged as a marked normalizer lift. Its
placement and remaining reflection, Cartan and braid equations remain
necessary before FiveData and the full marked comparisons.
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

/-- Both full rank-one Bruhat formulas on the same source quotient and
Cartan. The unitary element is its actual SU₃ Weyl image; identification
with a marked normalizer lift remains a separate source obligation. -/
theorem marked_rank_one_bruhat :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (H : (Eˣ × Eˣ) →* X ⧸ Q.D) (w : X ⧸ Q.D),
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      FivePositive.Relations (fiveForm J) r ∧
      (Function.Injective (chartWord Q r) ∧ Set.range (chartWord Q r) = (split.U : Set (X ⧸ Q.D)) ∧ r.generated = split.U) ∧
      H.range ≤ Q.tits.B ⊓ Q.tits.N ∧
      (∀ p a, H p*r.A (.ofAdd a)*(H p)⁻¹ = r.A (.ofAdd (((p.1:E)/(p.2:E))*a))) ∧
      (∀ p a, H p*r.C (.ofAdd a)*(H p)⁻¹ = r.C (.ofAdd (((p.1:E)*J.conj (p.2:E))*a))) ∧
      (∀ p v, H p*r.B v*(H p)⁻¹ = r.B (FiveTorus.scale (fiveForm J) p p.2 v)) ∧
      (∀ p v, H p*r.D v*(H p)⁻¹ = r.D (FiveTorus.scale (fiveForm J) p p.1 v)) ∧
      w = (θ (hermitianWeylSU J hJ) : X ⧸ Q.D) ∧ w*w = 1 ∧
      (s.val : X ⧸ Q.D)*s.val = 1 ∧
      (∀ p, (s.val : X ⧸ Q.D)*r.B p*s.val = r.D p) ∧
      (∀ p, (s.val : X ⧸ Q.D)*r.D p*s.val = r.B p) ∧
      (∀ a, (s.val : X ⧸ Q.D)*r.C (.ofAdd a)*s.val = r.C (.ofAdd (J.conj a))) ∧
      (∀ (a : E) (ha : a ≠ 0), (s.val : X ⧸ Q.D)*r.A (.ofAdd a)*s.val =
        r.A (.ofAdd a⁻¹)*H (FiveBruhat.aTorus a ha)*s.val*r.A (.ofAdd a⁻¹)) ∧
      ∀ (p : hermitianUnipotentCoord J) (hp : p.val.2 ≠ 0),
        w*r.B p*w = r.B (FiveBruhat.leftParameter (fiveForm J) p hp)*
          H (FiveBruhat.bTorus (fiveForm J) p hp)*w*r.B (FiveBruhat.rightParameter (fiveForm J) p hp) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c,ξ,k,hk0,hcover,hpanel,hb,hc,hA,hC,hD,hγ,hrel,hco,H,hH,hHmem,hHA,hHC,hHB,hHD⟩ :=
    marked_full_cartan_relations Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hHeq : H = fullUnitaryCartan Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA := by
    ext p
    exact hH p
  obtain ⟨hss,hsB,hsD⟩ := synchronizedRoots_linear_reflection Q split i j hVi s μ₀ J b ξ γ
  refine ⟨g,θ,b,γ,ξ,H,unitaryWeyl Q split j J hJ θ,hcover,hpanel,hb,hrel,hco,hHmem,
    hHA,hHC,hHB,hHD,rfl,unitaryWeyl_square Q split j J hJ θ,hss,hsB,hsD,hγ,?_,?_⟩
  · intro a ha
    rw [hHeq]
    exact fullUnitaryCartan_linear_bruhat Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA a ha
  · intro p hp
    rw [hHeq]
    exact fullUnitaryCartan_unitary_bruhat Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hA p hp

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

/-- The two rank-one Bruhat words and the linear reflection on literal
original representatives, with the original actor and projective square. -/
theorem original_rank_one_bruhat :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (H : (Eˣ × Eˣ) →* (generated L S) ⧸ Q.D) (w : (generated L S) ⧸ Q.D),
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      FivePositive.Relations (fiveForm J) r ∧
      Function.Injective (chartWord Q r) ∧
      Set.range (chartWord Q r) = ((S.subgroupOf (generated L S)).map Q.q : Set ((generated L S) ⧸ Q.D)) ∧
      H.range ≤ Q.tits.B ⊓ Q.tits.N ∧
      w = (θ (hermitianWeylSU J hJ) : (generated L S) ⧸ Q.D) ∧ w*w = 1 ∧
      (∀ (a : E) (ha : a ≠ 0) (W A : generated L S),
        Q.q W = s.val → Q.q A = r.A (.ofAdd a) →
        Q.q (W*A*W) = r.A (.ofAdd a⁻¹)*H (FiveBruhat.aTorus a ha)*s.val*r.A (.ofAdd a⁻¹)) ∧
      (∀ (p : hermitianUnipotentCoord J) (hp : p.val.2 ≠ 0) (W B : generated L S),
        Q.q W = w → Q.q B = r.B p →
        Q.q (W*B*W) = r.B (FiveBruhat.leftParameter (fiveForm J) p hp)*
          H (FiveBruhat.bTorus (fiveForm J) p hp)*w*r.B (FiveBruhat.rightParameter (fiveForm J) p hp)) ∧
      ∀ (p : hermitianUnipotentCoord J) (W B D : generated L S),
        Q.q W = s.val → Q.q B = r.B p → Q.q D = r.D p →
        Q.q (W*B*W) = r.D p ∧ Q.q (W*D*W) = r.B p := by
  dsimp only
  obtain ⟨g,θ,b,γ,ξ,H,w,hcover,hpanel,hb,hrel,hco,hHmem,hHA,hHC,hHB,hHD,hw,hww,hss,hsB,hsD,hsC,hsA,hwB⟩ :=
    marked_rank_one_bruhat Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,ξ,H,w,hcover,hpanel,hrel,hco.1,?_,hHmem,hw,hww,?_,?_,?_⟩
  · rw [quotient_sourceS_image_eq_unipotent h Q split]
    exact hco.2.1
  · intro a ha W A hW hA
    simpa only [map_mul,hW,hA] using hsA a ha
  · intro p hp W B hW hB
    simpa only [map_mul,hW,hB] using hwB p hp
  · intro p W B D hW hB hD
    simpa only [map_mul,hW,hB,hD] using And.intro (hsB p) (hsD p)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
