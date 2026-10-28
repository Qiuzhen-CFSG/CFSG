module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.LinearApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.FieldCompatibility

/-!
# Synchronized fields on the original U₅ source roots

Compare the same A–B commutator in the constructed natural SL₂ and SU₃
sections. This forces the common additive whole-root label to be a nonzero
scalar times a field isomorphism, and pins the A-root coefficient in the SU₃
section. The original actors, specified reflection, full nonabelian roots,
covering center and projective panel square are retained, including q=2,4.
The remaining center, mixed, Cartan and Weyl equations still require proofs
before FiveData and the full marked comparison can be constructed.
Source: Fong--Seitz II (8C), pp.203--208, (8.15)--(8.16), (8.21)--(8.23),
and the comparison of both natural actions in (8.32)--(8.33).
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

/-- Construct a multiplicatively compatible field label from the original
profile and covering inputs, with both actual natural actions preserved. -/
theorem marked_synchronized_fields :
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
      ℓ ≠ 0 ∧ k ≠ 0 ∧
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
          (d q : X ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,c₃,b,d,γ,hcover,hpanel,hc₃,hb,hd,hγ,hcross,k,hk0,hγc,hδ⟩ :=
    marked_reflected_root_coordinates Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hde : d = reflectedUnitaryChart Q split i j s b := by
    apply MulEquiv.ext
    intro p
    apply Subtype.ext
    rw [hd,reflectedUnitaryChart_apply,
      inv_eq_of_mul_eq_one_right (GTwoSource.sourceReflection_sq Q split i hVi μ₀ s)]
  subst d
  obtain ⟨c₂,hc₂,_,_,hker,_,hsurj,_⟩ := marked_linear_natural_section Q split e h J n hK hE hfixed hJ
    hm i j hij hVi hVj s f hf hk ν hindexi hindexj
  obtain ⟨ψ,hψ⟩ := linear_full_root_labels Q split i j hij hVi s μ₀ c₂ hc₂ J (NeZero.pos n) hE hfixed b hker hsurj
  let μ := (GTwoSource.alignedPinning Q split i hVi μ₀ s).symm
  have hcomm := unitary_opposite_commutator Q split J (NeZero.pos n) hK hE hfixed hJ hm i j hij hVi hVj s μ ν
  have hC : rootAt Q split i (Q.simple j) ≤ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
    rw [←hcomm]
    exact commutator_mono (opposite_roots_le_remainder Q split j i hij.symm).1
      (opposite_roots_le_remainder Q split j i hij.symm).2
  obtain ⟨ξ,hξ,hA⟩ := common_label_field Q split hm i j hij hVi hVj s μ₀ c₂ hc₂ c₃ J hE hfixed hJ
    θ b hb hc₃ ψ k hk0 hψ hδ hC
  have hψ1 : ψ 1 ≠ 0 := fun he => one_ne_zero (ψ.injective (he.trans ψ.map_zero.symm))
  refine ⟨g,θ,b,γ,c₂,c₃,ξ,ψ 1,k,hψ1,hk0,hcover,hpanel,hb,hc₂,hc₃,?_,?_,hγc,hδ,hγ,hcross⟩
  · intro p
    simpa only [hξ p.val.1] using hψ p
  · intro a
    simpa only [ξ.symm_apply_apply] using hA (ξ a)

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

/-- The original marked source has one multiplicative field label, used by
both whole unitary roots and the literal A–B commutator on Q.q representatives.
The commutator formula here is in the actual Frattini section. -/
theorem original_common_field_equations :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
      (c : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
        ≃ₗ[ZMod 2] (Fin 2 → K)) (ξ : E ≃+* K) (ℓ : K),
      let d := reflectedUnitaryChart Q split i j s b
      ℓ ≠ 0 ∧
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ p : hermitianUnipotentCoord J,
        linearSimpleCoordinate Q split i j hij c (b p) = .ofAdd (ℓ * ξ p.val.1) ∧
        linearCrossedCoordinate Q split i j hij c (d p) = .ofAdd (ℓ * ξ p.val.1)) ∧
      (∀ a : E, (s.val : (generated L S) ⧸ Q.D)*(γ (.ofAdd a) : (generated L S) ⧸ Q.D)*s.val =
        γ (.ofAdd (J.conj a))) ∧
      (∀ (p q : hermitianUnipotentCoord J) (B D : generated L S)
        (_hB : Q.q B = b p) (_hD : Q.q D = d q),
        Q.q (B*D) = Q.q D * (γ (.ofAdd (q.val.1*J.conj p.val.1)) : (generated L S) ⧸ Q.D) * Q.q B) ∧
      ∀ (a : E) (p : hermitianUnipotentCoord J) (A B : generated L S)
        (_hA : Q.q A = GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (ξ a)))
        (_hB : Q.q B = b p),
        ∃ w : simpleRemainder Q split i,
          (w : (generated L S) ⧸ Q.D) = Q.q (A*B*A⁻¹*B⁻¹) ∧
          c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) w)) =
            ![ℓ * ξ (a*p.val.1),0] := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  obtain ⟨g,θ,b,γ,c,c₃,ξ,ℓ,k,hℓ,_,hcover,hpanel,hb,hc,_,hlabels,_,_,_,hγ,hcross⟩ :=
    marked_synchronized_fields Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij
      hVi hVj s t f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,c,ξ,ℓ,hℓ,hcover,hpanel,hb,hlabels,hγ,?_,?_⟩
  · intro p q B D hB hD
    rw [map_mul,hB,hD]
    exact hcross p q
  · intro a p A B hA hB
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    let v := inclusion (opposite_roots_le_remainder Q split j i hij.symm).1 (b p)
    let w := remainderRankOneAction Q split i hVi
      (GTwoSource.alignedPinning Q split i hVi μ₀ s (Theory.PSL2.SemilinearCoverage.uni (ξ a))) v * v⁻¹
    refine ⟨w,?_,?_⟩
    · change (remainderRankOneAction Q split i hVi
        (GTwoSource.alignedPinning Q split i hVi μ₀ s (Theory.PSL2.SemilinearCoverage.uni (ξ a))) v : (generated L S) ⧸ Q.D) *
          (v : (generated L S) ⧸ Q.D)⁻¹ = _
      rw [remainderRankOneAction_apply,GTwoSource.alignedPinning_coe,
        ←GTwoSource.alignedSimpleParameter_apply]
      simp only [map_mul,map_inv,hA,hB]
      rfl
    · have hh := linear_mixed_coordinates Q split i j hij hVi s μ₀ c hc (ξ a) (b p)
      change c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) w)) =
        ![ξ a * (linearSimpleCoordinate Q split i j hij c (b p)).toAdd,0] at hh
      rw [hh]
      have hl := congrArg Multiplicative.toAdd (hlabels p).1
      change (linearSimpleCoordinate Q split i j hij c (b p)).toAdd = ℓ * ξ p.val.1 at hl
      rw [hl,map_mul ξ]
      congr 1
      ring

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
