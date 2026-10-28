module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.FieldApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.NaturalFlagPinning

/-!
# Full natural flags and mixed displacements on the original U₅ source

Start with the constructed common field and the two actual natural actions.
The specified unitary reflection identifies the simple linear root's image
as a Hermitian line. An explicit upper-root inner change puts that line on
the last axis, changes the actor marking and basis together, and preserves
the common fields, both full root charts, the projective panel square and
exact B–D crossing. The Hermitian pairing then puts the whole reflected
unitary root on the middle axis.

These full coordinates compute the literal original Q.q mixed displacement:
its first and middle entries are precisely the expected C and noncentral D
parameters. The central D correction still requires the source torus
argument; no full mixed equation or FiveData is assumed or concluded here.
Every positive binary degree and either endpoint orientation is retained.
Source: Fong--Seitz II (8C), (8.14)--(8.16), (8.24), pp.203--207.
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

/-- The two source natural actions and all four root charts admit one common
field and the full standard natural flag, with the original actor tracked. -/
theorem marked_synchronized_flags :
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
      (∀ p q : hermitianUnipotentCoord J,
        (b p : X ⧸ Q.D)*(d q : X ⧸ Q.D) =
          (d q : X ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) ) ∧
      (∀ a : E, (naturalSectionMap Q split j c₃
        (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a))).toAdd = ![0,0,k*J.conj a]) ∧
      (∀ a : E, (naturalSectionMap Q split j c₃
        (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0]) ∧
      ∀ p : hermitianUnipotentCoord J, (naturalSectionMap Q split j c₃
        (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d p))).toAdd = ![0,k*J.conj p.val.1,0] := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c₂,c₃,ξ,ℓ,k,hℓ,hk0,hcover,hpanel,hb,hc₂,hc₃,hlabels,hA,hγc,hδ,hγ,hcross⟩ :=
    marked_synchronized_fields Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hroot : ((rankOne Q split j).subtype.comp
      (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j := by
    ext y
    constructor
    · rintro ⟨q,rfl⟩
      change (θ (hermitianUnipotentSU J hJ q) : X ⧸ Q.D) ∈ _
      rw [←hb]
      exact (b q).property
    · intro hy
      obtain ⟨q,hq⟩ := b.surjective ⟨y,hy⟩
      exact ⟨q,(hb q).symm.trans (congrArg Subtype.val hq)⟩
  let av := fun a : E => linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a)
  have hav (a : E) : (av a : X ⧸ Q.D) ∈ simpleRoot Q split i := by
    rw [←GTwoSource.alignedSimpleParameter_range Q split i hVi μ₀ s]
    exact ⟨.ofAdd (ξ a),rfl⟩
  have ha1 : (naturalSectionMap Q split j c₃ (av 1)).toAdd 2 = k := by
    exact (hA 1).trans (by rw [map_one,mul_one])
  obtain ⟨p,hlast,hflag⟩ := exists_natural_flag_basis Q split j hVj c₃ J θ hc₃ hm i hij hVi t
    hE hfixed hJ hroot (av 1) (hav 1) (ha1 ▸ hk0)
  let u := hermitianUnipotentSU J hJ p
  let θ' := (MulAut.conj u).trans θ
  let b' := (MulAut.conj p).trans b
  let d := reflectedUnitaryChart Q split i j s b
  let d' := reflectedUnitaryChart Q split i j s b'
  let c' := unitaryBasisChange Q split j c₃ J u
  have hdin (q : hermitianUnipotentCoord J) : d' q = d (p*q*p⁻¹) := by
    apply Subtype.ext
    rfl
  have hc' (a : J.specialSubgroup) (v) :
      c' (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
        (θ' a) v) = Matrix.mulVec a.val.val (c' v) :=
    unitaryBasisChange_action Q split j hVj c₃ J θ hc₃ u a v
  have hroot' := repinned_root_range Q split j J θ hJ hroot p
  have hA' (a : E) : (naturalSectionMap Q split j c' (av a)).toAdd = ![0,0,k*J.conj a] := by
    exact (hflag (av a) (hav a)).trans (congrArg (fun z : E => ![0,0,z]) (hA a))
  have hγ' (a : E) : naturalCrossCoordinate Q split i j hij c' (γ (.ofAdd a)) = .ofAdd (k*J.conj a) := by
    have he := root_basis_cross Q split j hVj c₃ J θ hc₃ hm i hij hVi hE hfixed hJ hroot p
      (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a))) (γ (.ofAdd a)).property
    exact (congrArg (fun v : Fin 3 → E => Multiplicative.ofAdd (v 0)) he).trans (hγc a)
  have hδ' (q : hermitianUnipotentCoord J) :
      (naturalUnitaryCoordinate Q split hm i j hij c' (d' q)).toAdd = k*J.conj q.val.1 := by
    have he := root_basis_middle Q split j hVj c₃ J θ hc₃ hm i hij hVi hE hfixed hJ hroot p
      (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d' q)) (d' q).property
    change (naturalUnitaryCoordinate Q split hm i j hij c' (d' q)).toAdd =
      (naturalUnitaryCoordinate Q split hm i j hij c₃ (d' q)).toAdd at he
    rw [hdin,hδ,root_inner_first] at he
    exact he
  have hN0 : (naturalSectionMap Q split j c' (av 1)).toAdd = ![0,0,k] := by
    simpa only [map_one,mul_one] using hA' 1
  have hCfull (a : E) : (naturalSectionMap Q split j c'
      (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0] := by
    obtain ⟨h1,h2⟩ := crossed_root_natural_line J hE hfixed hJ Q split j hVj θ' hroot' c' hc'
      hm i hij hVi (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a))) (γ (.ofAdd a)).property
    ext r
    fin_cases r
    · exact congrArg Multiplicative.toAdd (hγ' a)
    · exact h1
    · exact h2
  have hDfull (q : hermitianUnipotentCoord J) : (naturalSectionMap Q split j c'
      (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d' q))).toAdd = ![0,k*J.conj q.val.1,0] := by
    obtain ⟨h0,h2⟩ := crossed_unitary_natural_axis Q split j hVj c' J θ' hc' hm i hij hVi t
      hE hfixed hJ hroot' (av 1) (hav 1)
      (congrFun hN0 0) (congrFun hN0 1) ((congrFun hN0 2) ▸ hk0)
      (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d' q)) (d' q).property
    ext r
    fin_cases r
    · exact h0
    · exact hδ' q
    · exact h2
  refine ⟨g*u,θ',b',γ,c₂,c',ξ,ℓ,k,hℓ,hk0,?_,?_,?_,hc₂,hc',?_,?_,hγ',hδ',hγ,?_,hA',hCfull,hDfull⟩
  · intro a
    change θ (u*a*u⁻¹) = _
    rw [hcover]
    congr 1
    group
  · intro a
    change ν (RootLocalCover.projection Q split j (θ (u*a*u⁻¹))) = _
    rw [hpanel]
    congr 1
    group
  · intro q
    change (b (p*q*p⁻¹) : X ⧸ Q.D) = θ (u*hermitianUnipotentSU J hJ q*u⁻¹)
    rw [hb]
    simp only [u,map_mul,map_inv]
  · intro q
    change linearSimpleCoordinate Q split i j hij c₂ (b (p*q*p⁻¹)) = _ ∧
      linearCrossedCoordinate Q split i j hij c₂ (d' q) = _
    rw [hdin]
    simpa only [root_inner_first] using hlabels (p*q*p⁻¹)
  · intro a
    exact (hlast (av a)).trans (hA a)
  · intro q r
    change (b (p*q*p⁻¹) : X ⧸ Q.D)*(d' r : X ⧸ Q.D) =
      (d' r : X ⧸ Q.D)*(γ (.ofAdd (r.val.1*J.conj q.val.1)) : X ⧸ Q.D)*(b (p*q*p⁻¹) : X ⧸ Q.D)
    rw [hdin]
    simpa only [root_inner_first,d] using hcross (p*q*p⁻¹) (p*r*p⁻¹)

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

/-- The full natural flag computes the actual original mixed displacement.
Only the central D coordinate remains invisible in this quotient formula. -/
theorem original_mixed_displacement_coordinates :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)) (ξ : E ≃+* K) (k : E),
      let d := reflectedUnitaryChart Q split i j s b
      k ≠ 0 ∧
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ a v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v)) ∧
      (∀ a : E, (naturalSectionMap Q split j c
        (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a))).toAdd = ![0,0,k*J.conj a]) ∧
      (∀ a : E, (naturalSectionMap Q split j c
        (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0]) ∧
      (∀ p : hermitianUnipotentCoord J, (naturalSectionMap Q split j c
        (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d p))).toAdd = ![0,k*J.conj p.val.1,0]) ∧
      (∀ p q : hermitianUnipotentCoord J,
        (b p : (generated L S) ⧸ Q.D)*(d q : (generated L S) ⧸ Q.D) =
          (d q : (generated L S) ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : (generated L S) ⧸ Q.D)*(b p : (generated L S) ⧸ Q.D)) ∧
      ∀ (a : E) (p : hermitianUnipotentCoord J) (A B : generated L S),
        Q.q A = GTwoSource.alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (ξ a)) →
        Q.q B = (b p : (generated L S) ⧸ Q.D) →
        ∃ v : simpleRemainder Q split j,
          (v : (generated L S) ⧸ Q.D) = Q.q (A⁻¹*B*A*B⁻¹) ∧
          (naturalSectionMap Q split j c v).toAdd =
            ![k*J.conj (a*J.conj p.val.2), k*J.conj (a*p.val.1), 0] := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,_,hk0,hcover,hpanel,hb,_,hc,_,_,_,_,_,hcross,hA,hC,hD⟩ :=
    marked_synchronized_flags Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,c,ξ,k,hk0,hcover,hpanel,hb,hc,hA,hC,hD,hcross,?_⟩
  intro a p A B hAv hBv
  let av := linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a)
  let bv := θ (hermitianUnipotentSU J hJ p)
  let v := av⁻¹ * remainderRankOneAction Q split j hVj bv av
  refine ⟨v,?_,?_⟩
  · change (av : (generated L S) ⧸ Q.D)⁻¹ *
      (remainderRankOneAction Q split j hVj bv av : (generated L S) ⧸ Q.D) = _
    rw [remainderRankOneAction_apply]
    rw [map_mul,map_mul,map_mul,map_inv,map_inv,hAv,hBv,hb]
    simp only [av,bv,μ₀,mul_assoc,linearRootInUnitaryRadical]
  · have he := hc (hermitianUnipotentSU J hJ p)
      (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) av))
    change c (.ofMul (remainderFrattiniAction Q split j hVj bv
      (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) av))) = _ at he
    rw [remainderFrattiniAction_mk] at he
    change (naturalSectionMap Q split j c (remainderRankOneAction Q split j hVj bv av)).toAdd =
      Matrix.mulVec (hermitianUnipotentMatrix J p) (naturalSectionMap Q split j c av).toAdd at he
    change (naturalSectionMap Q split j c (av⁻¹ * _)).toAdd = _
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,he,hA]
    ext r
    fin_cases r <;> simp [hermitianUnipotentMatrix,CharTwo.neg_eq,map_mul]
    all_goals try rw [J.conj_involutive]
    all_goals ring_nf
    all_goals simp only [CharTwo.two_eq_zero,mul_zero]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
