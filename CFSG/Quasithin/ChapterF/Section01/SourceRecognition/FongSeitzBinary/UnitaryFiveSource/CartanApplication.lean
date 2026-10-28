module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.PositiveApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.FullCartan

/-!
# Full Cartan actions on the original U₅ quotient

The original synchronized natural flag, full positive-root relations and
linear coroot actions construct the two-parameter Cartan inside B ∩ N.
All four weights use the literal presentation parameters. The original
application retains the generic covering map, its projective panel square,
the entire Sylow image, and every Q.q conjugation representative.
Every positive binary degree, including q=2 and q=4, is included.
Source: Fong--Seitz II (8C), pp.203–210, especially (8.24)–(8.37).
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

/-- Construct the full source Cartan with all four presentation actions,
retaining the marked natural flag for subsequent Weyl normalization. -/
theorem marked_full_cartan_relations :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)) (ξ : E ≃+* K) (k : E),
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      k ≠ 0 ∧
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ a v, c (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v)) ∧
      (∀ a : E, (naturalSectionMap Q split j c
        (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a))).toAdd = ![0,0,k*J.conj a]) ∧
      (∀ a : E, (naturalSectionMap Q split j c
        (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0]) ∧
      (∀ p : hermitianUnipotentCoord J, (naturalSectionMap Q split j c
        (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm)
          (reflectedUnitaryChart Q split i j s b p))).toAdd = ![0,k*J.conj p.val.1,0]) ∧
      (∀ a : E, (s.val : X ⧸ Q.D)*(γ (.ofAdd a) : X ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a))) ∧
      FivePositive.Relations (fiveForm J) r ∧
      (Function.Injective (chartWord Q r) ∧ Set.range (chartWord Q r) = (split.U : Set (X ⧸ Q.D)) ∧ r.generated = split.U) ∧
      ∃ H : (Eˣ × Eˣ) →* X ⧸ Q.D,
        (∀ p, H p = GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom p.1)*
          unitaryTorus Q split j J hJ θ (unitaryCartanParameter J p)) ∧
        H.range ≤ Q.tits.B ⊓ Q.tits.N ∧
        (∀ p a, H p*r.A (.ofAdd a)*(H p)⁻¹ = r.A (.ofAdd (((p.1:E)/(p.2:E))*a))) ∧
        (∀ p a, H p*r.C (.ofAdd a)*(H p)⁻¹ = r.C (.ofAdd (((p.1:E)*J.conj (p.2:E))*a))) ∧
        (∀ p v, H p*r.B v*(H p)⁻¹ = r.B (FiveTorus.scale (fiveForm J) p p.2 v)) ∧
        ∀ p v, H p*r.D v*(H p)⁻¹ = r.D (FiveTorus.scale (fiveForm J) p p.1 v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,hflags,hrel,hco,hLa,hLc,hLbd⟩ := marked_positive_root_relations Q split e h J n
    hK hE hfixed hJ hconj hm i j hij hVi hVj s t f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  rcases hflags with ⟨hℓ,hk0,hcover,hpanel,hb,hc₂,hc,hlabels,hA,hγc,hδ,hγ,hcross,hAfull,hCfull,hDfull⟩
  let H := fullUnitaryCartan Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hAfull
  refine ⟨g,θ,b,γ,c,ξ,k,hk0,hcover,hpanel,hb,hc,hAfull,hCfull,hDfull,hγ,hrel,hco,H,
    fun p => rfl,?_,?_⟩
  · rintro x ⟨p,rfl⟩
    exact fullUnitaryCartan_mem Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hAfull p
  · exact synchronizedRoots_full_cartan Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0
      hAfull γ hCfull hrel hLa hLc hLbd

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

/-- Full Cartan conjugation on literal original representatives, with
unique positive coverage of the original Sylow image and the original cover square. -/
theorem original_full_cartan_relations :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (H : (Eˣ × Eˣ) →* (generated L S) ⧸ Q.D),
      let r := synchronizedRoots Q split i j hVi s μ₀ J b γ ξ
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ v, (b v : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ v)) ∧
      FivePositive.Relations (fiveForm J) r ∧
      Function.Injective (chartWord Q r) ∧
      Set.range (chartWord Q r) = ((S.subgroupOf (generated L S)).map Q.q : Set ((generated L S) ⧸ Q.D)) ∧
      (∀ p, H p = GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom p.1)*
        unitaryTorus Q split j J hJ θ (unitaryCartanParameter J p)) ∧
      H.range ≤ Q.tits.B ⊓ Q.tits.N ∧
      (∀ (p : Eˣ × Eˣ) (a c : E) (T A C : generated L S),
        Q.q T = H p → Q.q A = r.A (.ofAdd a) → Q.q C = r.C (.ofAdd c) →
        Q.q (T*A*T⁻¹) = r.A (.ofAdd (((p.1:E)/(p.2:E))*a)) ∧
        Q.q (T*C*T⁻¹) = r.C (.ofAdd (((p.1:E)*J.conj (p.2:E))*c))) ∧
      ∀ (p : Eˣ × Eˣ) (v : hermitianUnipotentCoord J) (T B D : generated L S),
        Q.q T = H p → Q.q B = r.B v → Q.q D = r.D v →
        Q.q (T*B*T⁻¹) = r.B (FiveTorus.scale (fiveForm J) p p.2 v) ∧
        Q.q (T*D*T⁻¹) = r.D (FiveTorus.scale (fiveForm J) p p.1 v) := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  dsimp only
  obtain ⟨g,θ,b,γ,c,ξ,k,hk0,hcover,hpanel,hb,hc,hA,hC,hD,hγ,hrel,hco,H,hH,hHmem,hHA,hHC,hHB,hHD⟩ :=
    marked_full_cartan_relations Q split (originalMarkedIso Q) h J n
      hK hE hfixed hJ hconj hm i j hij hVi hVj s t f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,ξ,H,hcover,hpanel,hb,hrel,hco.1,?_,hH,hHmem,?_,?_⟩
  · rw [quotient_sourceS_image_eq_unipotent h Q split]
    exact hco.2.1
  · intro p a c T A C hT hA hC
    simpa only [map_mul,map_inv,hT,hA,hC] using And.intro (hHA p a) (hHC p c)
  · intro p v T B D hT hB hD
    simpa only [map_mul,map_inv,hT,hB,hD] using And.intro (hHB p v) (hHD p v)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
