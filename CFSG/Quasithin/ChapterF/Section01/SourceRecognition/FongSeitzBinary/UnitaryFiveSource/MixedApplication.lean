module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalFlagApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.MixedCollection

/-!
# The constructed U₅ mixed correction on the original source quotient

The original profiles and generic SU₃ cover construct the common field,
the full Hermitian root charts, both natural actors and the entire natural
flag. The same source displacement then constructs a Hermitian correction
T(p,a) and proves its first coordinate and the exact B–A collection law.
No correction function or mixed equation is supplied as an input.

The literal original Q.q product retains both full nonabelian roots,
the SU₃ cover and its projective panel square. Every positive binary degree,
including q=2 and q=4, and either endpoint orientation is retained.
The standard central coefficient, Cartan/Weyl equations and FiveData
assembly remain to be proved before this becomes source recognition.
Source: Fong--Seitz II (8C), (8.24), printed p.207.
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

/-- Construct the actual mixed correction from the original profiles,
with all common-field natural flags and actor markings retained. -/
theorem marked_mixed_root_correction :
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
      ∃ T : hermitianUnipotentCoord J → E → hermitianUnipotentCoord J,
        (∀ p a, (T p a).val.1 = a*p.val.1) ∧
        ∀ p a, (b p : X ⧸ Q.D)*GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (ξ a)) =
          GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (ξ a))*(d (T p a) : X ⧸ Q.D)*
            (γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,hℓ,hk0,hcover,hpanel,hb,hc₂,hc,hlabels,hA,hγc,hδ,hγ,hcross,hAfull,hCfull,hDfull⟩ :=
    marked_synchronized_flags Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  obtain ⟨T,hT,hBA⟩ := mixed_root_correction Q split hm i j hij hVi hVj s μ₀ J hJ θ b hb γ c hc
    ξ k hk0 hAfull hCfull hDfull
  exact ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,
    ⟨hℓ,hk0,hcover,hpanel,hb,hc₂,hc,hlabels,hA,hγc,hδ,hγ,hcross,hAfull,hCfull,hDfull⟩,
      T,hT,hBA⟩

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

/-- The constructed mixed correction gives an exact original Q.q product,
with the full unitary roots and the original special/projective marking. -/
theorem original_mixed_root_correction :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (T : hermitianUnipotentCoord J → E → hermitianUnipotentCoord J),
      let d := reflectedUnitaryChart Q split i j s b
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ p a, (T p a).val.1 = a*p.val.1) ∧
      ∀ (a : E) (p : hermitianUnipotentCoord J) (A B : generated L S),
        Q.q A = GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (ξ a)) →
        Q.q B = (b p : (generated L S) ⧸ Q.D) →
        Q.q (B*A) = Q.q A*(d (T p a) : (generated L S) ⧸ Q.D)*
          (γ (.ofAdd (a*J.conj p.val.2)) : (generated L S) ⧸ Q.D)*Q.q B := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  obtain ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,hflags,T,hT,hBA⟩ := marked_mixed_root_correction Q split
    (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  exact ⟨g,θ,b,γ,ξ,T,hflags.2.2.1,hflags.2.2.2.1,hflags.2.2.2.2.1,hT,
    fun a p A B hA hB => by rw [map_mul,hA,hB]; exact hBA p a⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
