module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalCrossingApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.DerivedRootApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.ReflectedRoots

/-!
# Original compatible whole-unitary-root coordinates

Combine the actual SU₃ natural section with the actual SL₂-derived Hermitian
module. The latter proves that the specified linear reflection moves a
crossed-linear root element. The reflected B–D pairing therefore selects
Hermitian conjugation and constructs compatible parameters for both entire
nonabelian unitary roots and their crossed linear root. Both centers remain
in these group isomorphisms. The B–D polynomial and the linear Weyl action
use the same field labels, including q = 2 and q = 4.

The covering actor, projective panel square and literal original Q.q products
are preserved. This discharges the coordinate compatibility needed for the
B–D equation. Matching the A-root and derived-center parameters, the remaining
mixed crossings and full Cartan/Weyl laws are still needed for FiveData.
Source: Fong--Seitz II (8C), (8.15)--(8.16), (8.21)--(8.23), pp.204,206--207.
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

include e h hK hE hfixed hJ hm hij hVi hVj s hf hk ν in
/-- The constructed derived module forces the specified linear reflection
to move an actual crossed-linear root element, in every positive degree. -/
theorem marked_linear_reflection_moves_crossed_root :
    ∃ z : rootAt Q split i (Q.simple j),
      (s.val : X ⧸ Q.D)*z*(s.val : X ⧸ Q.D) ≠ z := by
  obtain ⟨ξ,u,_,_,_,hC,_,_,_,hsC,_⟩ := marked_derived_root_relations Q split e h J n
    hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  let l := fieldRelabelledActor Q split i hVi μ₀ s n ξ
  let v := (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)).subtype.comp u.toMonoidHom
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  obtain ⟨a,ha⟩ := exists_conjugation_ne n
  have hi := derived_C_injective Q split n i l u
  refine ⟨⟨r.C (.ofAdd a),hC ▸ ⟨.ofAdd a,rfl⟩⟩,?_⟩
  intro hz
  apply ha
  exact congrArg Multiplicative.toAdd (hi ((hsC a).symm.trans hz))

include e h hK hE hfixed hJ hconj hm hij hVi hVj s t hf hk ν hπ hπν hindexi hindexj hQi hderived hfrattini

/-- Construct compatible coordinates on both entire nonabelian unitary roots
and the crossed linear root. The B–D equation and the specified linear Weyl
action now use the same Hermitian field labels. -/
theorem marked_reflected_root_coordinates :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E))
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (d : hermitianUnipotentCoord J ≃* rootAt Q split j (Q.simple i))
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)),
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) =
        J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ a v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v)) ∧
      (∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ p, (d p : X ⧸ Q.D) = (s.val : X ⧸ Q.D)*(b p : X ⧸ Q.D)*s.val) ∧
      (∀ a : E, (s.val : X ⧸ Q.D)*(γ (.ofAdd a) : X ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a))) ∧
      (∀ p q : hermitianUnipotentCoord J,
        (b p : X ⧸ Q.D)*(d q : X ⧸ Q.D) =
          (d q : X ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D)) ∧
      ∃ k : E, k ≠ 0 ∧
        (∀ a : E, naturalCrossCoordinate Q split i j hij c (γ (.ofAdd a)) = .ofAdd (k*J.conj a)) ∧
        ∀ p : hermitianUnipotentCoord J,
          (naturalUnitaryCoordinate Q split hm i j hij c (d p)).toAdd = k*J.conj p.val.1 := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨g,θ,c,χ,hcover,hpanel,hroot,hc,hχ,hδ,hker,hcross⟩ := marked_natural_crossing Q split e h J
    (NeZero.pos n) hE hfixed hJ hconj hm i j hij hVi hVj t ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  let b := pinnedUnitaryChart Q split j J hJ θ hroot
  let d := reflectedUnitaryChart Q split i j s b
  let δ := naturalUnitaryCoordinate Q split hm i j hij c
  have hb (p) : (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p) :=
    pinnedUnitaryChart_apply Q split j J hJ θ hroot p
  have hmixed (p : hermitianUnipotentCoord J) (v : rootAt Q split j (Q.simple i)) :
      (b p : X ⧸ Q.D)*v = v*(χ.symm (.ofAdd (p.val.1*(δ v).toAdd)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
    rw [hb]
    exact hcross p ⟨v,cross_root_le_own_remainder Q split hm j i hij.symm v.property⟩ v.property
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  have hss := GTwoSource.sourceReflection_sq Q split i hVi μ₀ s
  have hmove := marked_linear_reflection_moves_crossed_root Q split e h J n hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν
  obtain ⟨k,hk0,hd,hγ,hmixed'⟩ := reflected_unitary_labels Q split hm i j hij s hss J
    (NeZero.pos n) hE hfixed b χ δ hδ hker hVi hVj hmixed hmove
  let γ := normalizedCrossChart Q split i j J χ k hk0
  refine ⟨g,θ,c,b,d,γ,hcover,hpanel,hc,hb,?_,?_,hmixed',k,hk0,?_,hd⟩
  · intro p
    rw [reflectedUnitaryChart_apply,inv_eq_of_mul_eq_one_right hss]
  · intro a
    change (s.val : X ⧸ Q.D)*(χ.symm (.ofAdd (k*J.conj a)) : X ⧸ Q.D)*s.val =
      (χ.symm (.ofAdd (k*J.conj (J.conj a))) : X ⧸ Q.D)
    rw [J.conj_involutive]
    exact hγ a
  · intro a
    rw [←hχ,normalizedCrossChart_apply,χ.apply_symm_apply]

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

/-- The compatible whole-root crossing holds on literal original Q.q
products, with the same full SU₃ covering map and projective panel square. -/
theorem original_reflected_root_equations :
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (d : hermitianUnipotentCoord J ≃* rootAt Q split j (Q.simple i))
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)),
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) =
        J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ p, (d p : (generated L S) ⧸ Q.D) =
        (s.val : (generated L S) ⧸ Q.D)*(b p : (generated L S) ⧸ Q.D)*s.val) ∧
      (∀ a : E, (s.val : (generated L S) ⧸ Q.D)*
        (γ (.ofAdd a) : (generated L S) ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a))) ∧
      ∀ (p q : hermitianUnipotentCoord J) (B D : generated L S)
        (_hB : Q.q B = b p) (_hD : Q.q D = d q),
        Q.q (B*D) = Q.q D * (γ (.ofAdd (q.val.1*J.conj p.val.1)) : (generated L S) ⧸ Q.D) * Q.q B := by
  obtain ⟨g,θ,c,b,d,γ,hcover,hpanel,_,hb,hd,hγ,hcross,_⟩ :=
    marked_reflected_root_coordinates Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj
      hm i j hij hVi hVj s t f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,d,γ,hcover,hpanel,hb,hd,hγ,?_⟩
  intro p q B D hB hD
  rw [map_mul,hB,hD]
  exact hcross p q

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
