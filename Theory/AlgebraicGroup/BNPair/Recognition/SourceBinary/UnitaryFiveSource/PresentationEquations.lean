module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.MarkedReflection
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePresentation

/-!
# Presentation equations for the synchronized U₅ source

The positive relations, four full-Cartan actions, exact rank-one Bruhat
words and six whole-root reflection equations instantiate every relation
scheme of FivePresentation. This boundary retains the actual normalizer
lifts. Its three remaining inputs are precisely the two Cartan reflection
identities and the braid; the source constructor discharges these using
WeylCartan, on the same witnesses.
Source: Fong--Seitz II (8C), pp.203–210; Steinberg, Lectures on Chevalley
Groups, Theorem 33 and Lemmas 63–64.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
variable {X E K : Type*} [Group X] [Field E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) E]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (ξ : E ≃+* K) (k : E) (hk : k ≠ 0)
local notation "A" => fun a : E => alignedSimpleParameter Q split i hVi μ s (Multiplicative.ofAdd (ξ a))
local notation "av" => fun a : E => linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a)
local notation "N" => naturalSectionMap Q split j c
variable (hA : ∀ a : E, (naturalSectionMap Q split j c
  (linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a))).toAdd = ![0,0,k*J.conj a])

variable (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
  (hC : ∀ a : E, (naturalSectionMap Q split j c (inclusion (opposite_roots_le_remainder Q split i j hij).2
    (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0])
  (t : RootReflection Q split j)


local notation "R" => synchronizedRoots Q split i j hVi s μ J b γ ξ
local notation "H" => fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA
local notation "w" => unitaryWeyl Q split j J hJ θ
variable (hm : rotationOrder Q = 4)
  (hrel : FivePositive.Relations (fiveForm J) (synchronizedRoots Q split i j hVi s μ J b γ ξ))
  (hHA : ∀ p a, (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*((synchronizedRoots Q split i j hVi s μ J b γ ξ)).A (.ofAdd a)*((fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p)⁻¹ = ((synchronizedRoots Q split i j hVi s μ J b γ ξ)).A (.ofAdd (((p.1:E)/(p.2:E))*a)))
  (hHC : ∀ p a, (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*((synchronizedRoots Q split i j hVi s μ J b γ ξ)).C (.ofAdd a)*((fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p)⁻¹ = ((synchronizedRoots Q split i j hVi s μ J b γ ξ)).C (.ofAdd (((p.1:E)*J.conj (p.2:E))*a)))
  (hHB : ∀ p v, (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*((synchronizedRoots Q split i j hVi s μ J b γ ξ)).B v*((fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p)⁻¹ = ((synchronizedRoots Q split i j hVi s μ J b γ ξ)).B (FiveTorus.scale (fiveForm J) p p.2 v))
  (hHD : ∀ p v, (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*((synchronizedRoots Q split i j hVi s μ J b γ ξ)).D v*((fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p)⁻¹ = ((synchronizedRoots Q split i j hVi s μ J b γ ξ)).D (FiveTorus.scale (fiveForm J) p p.1 v))
  (hsC : ∀ a : E, (s.val : X ⧸ Q.D)*(γ (.ofAdd a) : X ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a)))
  (hsh : ∀ p, (s.val : X ⧸ Q.D)*(fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*s.val = (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) (p.2,p.1))
  (hth : ∀ p, (unitaryWeyl Q split j J hJ θ)*(fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) p*(unitaryWeyl Q split j J hJ θ) = (fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA) (p.1,(Units.map J.conj.toMonoidHom p.2)⁻¹))
  (hst : ((s.val : X ⧸ Q.D)*(unitaryWeyl Q split j J hJ θ))^4 = 1)

include hb hc hk hA hC t hm hrel hHA hHC hHB hHD hsC hsh hth hst in
/-- All presentation equations on the synchronized whole source roots. -/
theorem synchronizedRoots_satisfies :
    (FivePresentation.parameters (fiveForm J)).Satisfies
      (Presentation.Generator.ofMaps R H (s.val : X ⧸ Q.D) w) := by
  obtain ⟨hss,hsB,hsD⟩ := synchronizedRoots_linear_reflection Q split i j hVi s μ J b ξ γ
  intro x y he
  cases he <;> simp only [Presentation.a,Presentation.d,Presentation.c,Presentation.b,
    Presentation.h,Presentation.s,Presentation.t,map_one,map_mul,map_inv,map_pow,
    FreeGroup.lift_apply_of,Presentation.Generator.ofMaps]
  case ad a d => exact (hrel.AD a d).eq
  case cd c d => exact (hrel.CD c d).eq
  case bc b c => exact (hrel.BC b c).eq
  case ca c a => exact hrel.CA a.toAdd c.toAdd
  case bd b d => exact hrel.BD b d
  case ba b a => exact hrel.BA a.toAdd b
  case ha p a => exact hHA p a.toAdd
  case hd p d => exact hHD p d
  case hc p c => exact hHC p c.toAdd
  case hb p b => exact hHB p b
  case ss => exact hss
  case tt => exact unitaryWeyl_square Q split j J hJ θ
  case st => exact hst
  case sh p => exact hsh p
  case th p => exact hth p
  case sd d => exact hsD d
  case sc a => exact hsC a.toAdd
  case sb b => exact hsB b
  case ta a => exact unitaryWeyl_A Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t a.toAdd
  case td d => exact unitaryWeyl_D Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t hm hrel d
  case tc a => exact unitaryWeyl_C Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t a.toAdd
  case sa a ha => exact fullUnitaryCartan_linear_bruhat Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA a.toAdd (by simpa using ha)
  case tb p hp => exact fullUnitaryCartan_unitary_bruhat Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA p (FiveBruhat.snd_ne_zero (fiveForm J) hp)

include hb hc hk hA hC t hm hrel hHA hHC hHB hHD hsC hsh hth hst in
/-- The same equations for the actual normalizer lifts. -/
theorem synchronizedWeylLifts_satisfies :
    let lifts := synchronizedWeylLifts Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
    (FivePresentation.parameters (fiveForm J)).Satisfies
      (Presentation.Generator.ofMaps R H (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D)) := by
  dsimp only
  rw [synchronizedWeylLifts_s,synchronizedWeylLifts_t]
  exact synchronizedRoots_satisfies Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t hm
    hrel hHA hHC hHB hHD hsC hsh hth hst

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
