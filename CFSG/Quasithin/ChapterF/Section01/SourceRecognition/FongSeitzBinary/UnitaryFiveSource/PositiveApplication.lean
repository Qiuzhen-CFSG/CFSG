module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.MixedApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.PositiveRelations

/-!
# All positive U₅ equations on the original source quotient

The original profiles and generic SU₃ cover construct the common field,
the full nonabelian root charts and the marked natural flags. The actual
linear Cartan word now determines the complete B–A norm correction;
polarizing its central parameter gives the C–A trace equation. Together
with the proved B–D law and source commutators this constructs every
FivePositive relation on the same quotient and the same four charts.

The ordered-root theorem retains unique coverage of the original Sylow
image. The actual linear coroot acts on both whole unitary roots, including
their centers. Literal Q.q product and conjugation equations keep the
original maps, full Borel input, SU₃ cover and projective panel square.
All positive binary degrees, in particular q=2 and q=4, remain included.
Full Cartan/Weyl equations and marked FiveData comparison are still required.
Source: Fong--Seitz II (8C), (8.20)--(8.31), printed pp.206--209.
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

/-- Construct all positive relations with the same natural flags and original actor markings. -/
theorem marked_positive_root_relations :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
      (c₂ : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
        ≃ₗ[ZMod 2] (Fin 2 → K))
      (c₃ : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)) (ξ : E ≃+* K) (ℓ : K) (k : E),
      let d := reflectedUnitaryChart Q split i j s b
      (ℓ ≠ 0 ∧ k ≠ 0 ∧
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ a v, c₂ (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)
        (GTwoSource.alignedPinning Q split i hVi μ₀ s a) v) = Matrix.mulVec a.val (c₂ v)) ∧
      (∀ a v, c₃ (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c₃ v)) ∧
      (∀ p : hermitianUnipotentCoord J,
        linearSimpleCoordinate Q split i j hij c₂ (b p) = .ofAdd (ℓ * ξ p.val.1) ∧
        linearCrossedCoordinate Q split i j hij c₂ (d p) = .ofAdd (ℓ * ξ p.val.1)) ∧
      (∀ a : E, (naturalSectionMap Q split j c₃
        (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a))).toAdd 2 = k*J.conj a) ∧
      (∀ a : E, naturalCrossCoordinate Q split i j hij c₃ (γ (.ofAdd a)) = .ofAdd (k*J.conj a)) ∧
      (∀ p : hermitianUnipotentCoord J,
        (naturalUnitaryCoordinate Q split hm i j hij c₃ (d p)).toAdd = k*J.conj p.val.1) ∧
      (∀ a : E, (s.val : X ⧸ Q.D)*(γ (.ofAdd a) : X ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a))) ∧
      (∀ p q : hermitianUnipotentCoord J,
        (b p : X ⧸ Q.D)*(d q : X ⧸ Q.D) =
          (d q : X ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) ) ∧
      (∀ a : E, (naturalSectionMap Q split j c₃
        (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a))).toAdd = ![0,0,k*J.conj a]) ∧
      (∀ a : E, (naturalSectionMap Q split j c₃
        (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0]) ∧
      ∀ p : hermitianUnipotentCoord J, (naturalSectionMap Q split j c₃
        (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d p))).toAdd = ![0,k*J.conj p.val.1,0] ) ∧
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      FivePositive.Relations (fiveForm J) r ∧
      (Function.Injective (chartWord Q r) ∧ Set.range (chartWord Q r) = (split.U : Set (X ⧸ Q.D)) ∧ r.generated = split.U) ∧
      (∀ (u : Eˣ) (a : E),
        let H := GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom u)
        H*r.A (.ofAdd a)*H⁻¹ = r.A (.ofAdd ((u:E)^2*a))) ∧
      (∀ (u : Eˣ) (c : E),
        let H := GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom u)
        H*r.C (.ofAdd c)*H⁻¹ = r.C (.ofAdd (((u:E)/J.conj (u:E))*c))) ∧
      ∀ (u : Eˣ) (p : hermitianUnipotentCoord J),
        let H := GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom u)
        H*(b p : X ⧸ Q.D)*H⁻¹ = b (FivePositive.normParameter (fiveForm J) (↑u⁻¹ : E) p) ∧
        H*(d p : X ⧸ Q.D)*H⁻¹ = d (FivePositive.normParameter (fiveForm J) (u : E) p) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,hflags,T,hT,hBA⟩ := marked_mixed_root_correction Q split e h J n
    hK hE hfixed hJ hconj hm i j hij hVi hVj s t f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  rcases hflags with ⟨hℓ,hk0,hcover,hpanel,hb,hc₂,hc,hlabels,hA,hγc,hδ,hγ,hcross,hAfull,hCfull,hDfull⟩
  have hnorm := mixed_correction_eq_norm Q split hm i j hij hVi hVj s μ₀ J hJ θ b hb γ c hc
    ξ k hk0 hCfull hDfull hγ T hT hBA
  have hBAfull (p : hermitianUnipotentCoord J) (a : E) :
      (b p : X ⧸ Q.D)*GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (ξ a)) =
        GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (ξ a))*
          (reflectedUnitaryChart Q split i j s b (FivePositive.normParameter (fiveForm J) a p) : X ⧸ Q.D)*
          (γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by rw [hBA,hnorm]
  have hfirst (x : E) : ∃ p : hermitianUnipotentCoord J, p.val.1 = x := by
    obtain ⟨p,hp⟩ := HermitianForm.BinaryRootFrattini.firstCoordinate_surjective J hE hfixed (.ofAdd x)
    exact ⟨p,congrArg Multiplicative.toAdd hp⟩
  refine ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,
    ⟨hℓ,hk0,hcover,hpanel,hb,hc₂,hc,hlabels,hA,hγc,hδ,hγ,hcross,hAfull,hCfull,hDfull⟩,
    synchronizedRoots_relations Q split i j hVi s μ₀ J b γ ξ hm hij hVj hBAfull hcross,
    synchronizedRoots_coordinates Q split i j hVi s μ₀ J b γ ξ hm hij,
    synchronizedRoots_linear_cartan Q split i j hVi s μ₀ J b γ ξ hfirst hcross
      (mixed_linear_cartan_B Q split hm i j hij hVi hVj s μ₀ J hJ θ b hb γ c hc ξ k hk0
        hCfull hDfull hγ T hT hBA)
      (mixed_linear_cartan_D Q split hm i j hij hVi hVj s μ₀ J hJ θ b hb γ c hc ξ k hk0
        hCfull hDfull hγ T hT hBA)⟩

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

/-- All positive equations and the linear Cartan action hold on literal original Q.q representatives. -/
theorem original_positive_root_relations :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K),
      let d := reflectedUnitaryChart Q split i j s b
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      FivePositive.Relations (fiveForm J) r ∧
      Function.Injective (chartWord Q r) ∧
      Set.range (chartWord Q r) = ((S.subgroupOf (generated L S)).map Q.q : Set ((generated L S) ⧸ Q.D)) ∧
      (∀ (a : E) (p : hermitianUnipotentCoord J) (A B : generated L S),
        Q.q A = r.A (.ofAdd a) → Q.q B = r.B p →
        Q.q (B*A) = Q.q A*r.D (FivePositive.normParameter (fiveForm J) a p)*
          r.C (.ofAdd (a*J.conj p.val.2))*Q.q B) ∧
      (∀ (a c : E) (A C : generated L S),
        Q.q A = r.A (.ofAdd a) → Q.q C = r.C (.ofAdd c) →
        Q.q (C*A) = Q.q A*r.D (FivePositive.traceParameter (fiveForm J) a c)*Q.q C) ∧
      (∀ (u : Eˣ) (a c : E) (H A C : generated L S),
        Q.q H = GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom u) →
        Q.q A = r.A (.ofAdd a) → Q.q C = r.C (.ofAdd c) →
        Q.q (H*A*H⁻¹) = r.A (.ofAdd ((u:E)^2*a)) ∧
        Q.q (H*C*H⁻¹) = r.C (.ofAdd (((u:E)/J.conj (u:E))*c))) ∧
      ∀ (u : Eˣ) (p : hermitianUnipotentCoord J) (H B D : generated L S),
        Q.q H = GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom u) →
        Q.q B = (b p : (generated L S) ⧸ Q.D) → Q.q D = (d p : (generated L S) ⧸ Q.D) →
        Q.q (H*B*H⁻¹) = b (FivePositive.normParameter (fiveForm J) (↑u⁻¹ : E) p) ∧
        Q.q (H*D*H⁻¹) = d (FivePositive.normParameter (fiveForm J) (u : E) p) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  obtain ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,hflags,hrel,hco,hcartanA,hcartanC,hcartan⟩ := marked_positive_root_relations Q split
    (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,ξ,hflags.2.2.1,hflags.2.2.2.1,hflags.2.2.2.2.1,hrel,hco.1,?_,?_,?_,?_,?_⟩
  · rw [quotient_sourceS_image_eq_unipotent h Q split]
    exact hco.2.1
  · intro a p A B hA hB
    rw [map_mul,hA,hB]
    exact hrel.BA a p
  · intro a c A C hA hC
    rw [map_mul,hA,hC]
    exact hrel.CA a c
  · intro u a c H A C hH hA hC
    simpa only [map_mul,map_inv,hH,hA,hC] using And.intro (hcartanA u a) (hcartanC u c)
  · intro u p H B D hH hB hD
    simpa only [map_mul,map_inv,hH,hB,hD] using hcartan u p

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
