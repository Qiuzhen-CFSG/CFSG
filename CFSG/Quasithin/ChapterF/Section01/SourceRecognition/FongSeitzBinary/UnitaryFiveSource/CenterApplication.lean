module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.FieldApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.CenterCompatibility


/-!
# Common-field coordinates on the original U₅ root centers

The original profile and generic cover construct the compatible whole B,
D and C charts and the common SU₃/SL₂ field. Comparing these with the
actual derived Hermitian module identifies its C coordinate and both root
centers by one nonzero fixed-field scalar. The field comparison preserves
the Frobenius involution, so the original Q.q product formulas use the
actual unitary trace and norm over that same field.

The special unitary covering, its projective panel square, the specified
linear reflection and both natural actions remain explicit. Every positive
binary degree is retained, including q=2 and q=4. The noncentral B–A law
and the full Cartan/Weyl equations remain necessary for FiveData.
Source: Fong--Seitz II (8C), pp.206--207, (8.21)--(8.23) and (8.30).
-/

open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
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

/-- The original source constructs synchronized full roots and derived-center
charts using one common field and one nonzero fixed-field scalar. -/
theorem marked_synchronized_derived_centers :
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
      ∀ p q : hermitianUnipotentCoord J,
        (b p : X ⧸ Q.D)*(d q : X ⧸ Q.D) =
          (d q : X ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) ) ∧
      ∃ (η : K ≃+* Field n)
        (u : Multiplicative (Space n) ≃*
          (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)))
        (t₀ : HermitianForm.BorelTorus.EvenCenterAction.fixedField J),
        let l := fieldRelabelledActor Q split i hVi μ₀ s n η
        let v := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).subtype.comp u.toMonoidHom
        let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
        let ζ := η.symm.trans ξ.symm
        (∀ (a : SL(2,Field n)) (p : Space n),
          l a * (u (.ofAdd p) : X ⧸ Q.D) * (l a)⁻¹ = u (.ofAdd (action n a p))) ∧
        FourPositive.Relations (Field n) (conjugation n) (conjugation_involutive n) r ∧
        t₀ ≠ 0 ∧
        (∀ a : Field n, ζ (conjugation n a) = J.conj (ζ a)) ∧
        (∀ a : Field n, r.A (.ofAdd a) = GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (η.symm a))) ∧
        (∀ a : Field n, r.C (.ofAdd a) = (γ (.ofAdd ((t₀:E)*ζ a)) : X ⧸ Q.D)) ∧
        ∀ z : fixedField n, ∃ z' : HermitianForm.BorelTorus.EvenCenterAction.fixedField J,
          (z':E) = (t₀:E)*ζ (z:Field n) ∧
          r.B (.ofAdd z) = (b (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J (.ofAdd z')) : X ⧸ Q.D) ∧
          r.D (.ofAdd z) = (d (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J (.ofAdd z')) : X ⧸ Q.D) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c₂,c₃,ξ,ℓ,k,hℓ,hk0,hcover,hpanel,hb,hc₂,hc₃,hlabels,hA,hγc,hδ,hγ,hcross⟩ :=
    marked_synchronized_fields Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,c₂,c₃,ξ,ℓ,k,⟨hℓ,hk0,hcover,hpanel,hb,hc₂,hc₃,hlabels,hA,hγc,hδ,hγ,hcross⟩,?_⟩
  obtain ⟨η,u,hu,hrA,hrB,hrC,hrD,hr,hsB,_,_⟩ := marked_derived_root_relations Q split e h J n
    hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν
  let l := fieldRelabelledActor Q split i hVi μ₀ s n η
  let v := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).subtype.comp u.toMonoidHom
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  have hAparam (a : Field n) : r.A (.ofAdd a) = GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (η.symm a)) := by
    change fieldRelabelledActor Q split i hVi μ₀ s n η (Theory.PSL2.SemilinearCoverage.uni a) = _
    exact fieldRelabelledActor_upper Q split i hVi μ₀ s n η a
  have hZ := (unitary_simpleRoot_special Q split J (NeZero.pos n) hE hfixed hJ j hVj ν).2
  obtain ⟨t₀,ht₀,hCparam,hBparam⟩ := derived_center_synchronization Q split hm i j hij hVi hVj s μ₀ c₃ J
    (NeZero.pos n) hE hfixed hJ θ b hb hc₃ γ k hk0 hγc ξ hA hZ
      (conjugation n) (conjugation_involutive n) r hr η.symm hAparam hrB hrC hrD
      (derived_B_injective Q split n i l u) hsB
  have hζ (a : Field n) : (η.symm.trans ξ.symm) (conjugation n a) =
      J.conj ((η.symm.trans ξ.symm) a) := by
    rw [conjugation,iterateFrobeniusEquiv_def,map_pow,hconj]
  exact ⟨η,u,t₀,hu,hr,ht₀,hζ,hAparam,hCparam,hBparam⟩

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

/-- Both actual root centers and the crossed root use the same scalar and
common field, including the literal original central B–A product. -/
theorem original_synchronized_derived_centers :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
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
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
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
      (∀ a : E, (s.val : (generated L S) ⧸ Q.D)*(γ (.ofAdd a) : (generated L S) ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a))) ∧
      ∀ p q : hermitianUnipotentCoord J,
        (b p : (generated L S) ⧸ Q.D)*(d q : (generated L S) ⧸ Q.D) =
          (d q : (generated L S) ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : (generated L S) ⧸ Q.D)*(b p : (generated L S) ⧸ Q.D) ) ∧
      ∃ (η : K ≃+* Field n)
        (u : Multiplicative (Space n) ≃*
          (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup ((generated L S) ⧸ Q.D)))
        (t₀ : HermitianForm.BorelTorus.EvenCenterAction.fixedField J),
        let l := fieldRelabelledActor Q split i hVi μ₀ s n η
        let v := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup ((generated L S) ⧸ Q.D)).subtype.comp u.toMonoidHom
        let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
        let ζ := η.symm.trans ξ.symm
        (∀ (a : SL(2,Field n)) (p : Space n),
          l a * (u (.ofAdd p) : (generated L S) ⧸ Q.D) * (l a)⁻¹ = u (.ofAdd (action n a p))) ∧
        FourPositive.Relations (Field n) (conjugation n) (conjugation_involutive n) r ∧
        t₀ ≠ 0 ∧
        (∀ a : Field n, ζ (conjugation n a) = J.conj (ζ a)) ∧
        (∀ a : Field n, r.A (.ofAdd a) = GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (η.symm a))) ∧
        (∀ a : Field n, r.C (.ofAdd a) = (γ (.ofAdd ((t₀:E)*ζ a)) : (generated L S) ⧸ Q.D)) ∧
        (∀ z : fixedField n, ∃ z' : HermitianForm.BorelTorus.EvenCenterAction.fixedField J,
          (z':E) = (t₀:E)*ζ (z:Field n) ∧
          r.B (.ofAdd z) = (b (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J (.ofAdd z')) : (generated L S) ⧸ Q.D) ∧
          r.D (.ofAdd z) = (d (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J (.ofAdd z')) : (generated L S) ⧸ Q.D) ) ∧
        (∀ (a : Field n) (z : fixedField n) (A B : generated L S)
          (_hA : Q.q A = r.A (.ofAdd a)) (_hB : Q.q B = r.B (.ofAdd z)),
          ∃ z' : HermitianForm.BorelTorus.EvenCenterAction.fixedField J,
            (z':E) = ζ a * J.conj (ζ a) * ((t₀:E)*ζ (z:Field n)) ∧
            Q.q (B*A) = Q.q A *
              (d (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J (.ofAdd z')) : (generated L S) ⧸ Q.D) *
                (γ (.ofAdd (ζ a*((t₀:E)*ζ (z:Field n)))) : (generated L S) ⧸ Q.D) * Q.q B) ∧
        ∀ (a c : Field n) (A C : generated L S)
          (_hA : Q.q A = r.A (.ofAdd a)) (_hC : Q.q C = r.C (.ofAdd c)),
          ∃ z' : HermitianForm.BorelTorus.EvenCenterAction.fixedField J,
            (z':E) = ζ a * J.conj ((t₀:E)*ζ c) + J.conj (ζ a)*((t₀:E)*ζ c) ∧
            Q.q (C*A) = Q.q A *
              (d (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J (.ofAdd z')) : (generated L S) ⧸ Q.D) * Q.q C := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  obtain ⟨g,θ,b,γ,c₂,c₃,ξ,ℓ,k,hfields,η,u,t₀,hu,hr,ht₀,hζ,hAparam,hCparam,hBparam⟩ :=
    marked_synchronized_derived_centers Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,c₂,c₃,ξ,ℓ,k,hfields,η,u,t₀,hu,hr,ht₀,hζ,hAparam,hCparam,hBparam,?_⟩
  constructor
  · intro a z A B hA hB
    obtain ⟨z',hz',_,hD⟩ := hBparam (FourPositive.normParameter (Field n) (conjugation n) (conjugation_involutive n) a z)
    refine ⟨z',?_,?_⟩
    · rw [hz']
      change (t₀:E) * (η.symm.trans ξ.symm)
        (a * conjugation n a * (z:Field n)) = _
      rw [map_mul,map_mul,hζ]
      ring
    · rw [map_mul,hA,hB]
      have hf : (t₀:E) * (η.symm.trans ξ.symm) (a*(z:Field n)) =
          (η.symm.trans ξ.symm) a * ((t₀:E)*(η.symm.trans ξ.symm) (z:Field n)) := by
        rw [map_mul]
        ring
      have hc := (hCparam (a*(z:Field n))).trans
        (congrArg (fun v : E => (γ (.ofAdd v) : (generated L S) ⧸ Q.D)) hf)
      exact (hr.BA a z).trans
        (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl hD) hc) rfl)

  · intro a c A C hA hC
    obtain ⟨z',hz',_,hD⟩ := hBparam
      (FourPositive.traceParameter (Field n) (conjugation n) (conjugation_involutive n) a c)
    refine ⟨z',?_,?_⟩
    · rw [hz']
      change (t₀:E) * (η.symm.trans ξ.symm)
        (a * conjugation n c + conjugation n a * c) = _
      rw [map_add,map_mul,map_mul,hζ,hζ,map_mul J.conj,
        HermitianForm.BorelTorus.EvenCenterAction.fixedField_mem J t₀]
      ring
    · rw [map_mul,hA,hC]
      exact (hr.CA a c).trans
        (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl hD) rfl)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
