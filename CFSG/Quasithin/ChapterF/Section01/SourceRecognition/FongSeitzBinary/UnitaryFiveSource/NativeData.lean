module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NativeAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.WeylApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.PresentationEquations
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.WeylCartan

/-!
# Construction of FiveData from the original U₅ source

The same synchronized source charts supply all positive, Cartan, reflection,
Bruhat and braid equations. Original unipotent generation and the two actual
marked lifts then construct FiveData. The conclusion retains the supplied
SU₃ covering and projective square, the full positive subgroup, exact
Cartan formula and both normalizer representatives. Every positive binary
degree is admitted, including q=2 and q=4.
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

/-- Construct the genuine presentation data on the original marked
quotient, preserving its source charts, cover, full Sylow and Weyl lifts. -/
theorem marked_native_data :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (d : UnitaryPresentation.FiveData Q split j (fiveForm J)),
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      d.roots = synchronizedRoots Q split i j hVi s μ₀ J b γ ξ ∧
      (Function.Injective (chartWord Q d.roots) ∧
        Set.range (chartWord Q d.roots) = (split.U : Set (X ⧸ Q.D)) ∧ d.roots.generated = split.U) ∧
      (∀ p, d.cartan p = GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom p.1)*
        unitaryTorus Q split j J hJ θ (unitaryCartanParameter J p)) ∧
      d.lifts.s = s.val ∧
      (d.lifts.t : X ⧸ Q.D) = unitaryWeyl Q split j J hJ θ ∧
      ∃ u : Eˣ, (t.val : X ⧸ Q.D) = unitaryTorus Q split j J hJ θ u * d.lifts.t := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨g,θ,b,γ,c₂,c,ξ,ℓ,k,hflags,hrel,hco,hLa,hLc,hLbd⟩ :=
    marked_positive_root_relations Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  rcases hflags with ⟨hℓ,hk0,hcover,hpanel,hb,hc₂,hc,hlabels,hA,hγc,hδ,hγ,hcross,hAfull,hCfull,hDfull⟩
  let H := fullUnitaryCartan Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hAfull
  let lifts := synchronizedWeylLifts Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hAfull γ hCfull t
  have hHmem : H.range ≤ Q.tits.B ⊓ Q.tits.N := by
    rintro x ⟨p,rfl⟩
    exact fullUnitaryCartan_mem Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hAfull p
  obtain ⟨hHA,hHC,hHB,hHD⟩ := synchronizedRoots_full_cartan Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc
    ξ k hk0 hAfull γ hCfull hrel hLa hLc hLbd
  have hfirst (x : E) : ∃ p : hermitianUnipotentCoord J, p.val.1 = x := by
    obtain ⟨p,hp⟩ := HermitianForm.BinaryRootFrattini.firstCoordinate_surjective J hE hfixed (.ofAdd x)
    exact ⟨p,congrArg Multiplicative.toAdd hp⟩
  obtain ⟨hsh,hth,hst⟩ := fullUnitaryCartan_weyl_relations Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc
    ξ k hk0 hAfull γ hCfull t hHA hHC hm hrel hfirst (fun u p => (hLbd u p).2)
  have heq := synchronizedWeylLifts_satisfies Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0
    hAfull γ hCfull t hm hrel hHA hHC hHB hHD hγ hsh hth hst
  let d := nativeFiveData Q split e h (fiveForm J)
    (synchronizedRoots Q split i j hVi s μ₀ J b γ ξ) H lifts hco.2.2 hHmem heq
  have ht : (d.lifts.t : X ⧸ Q.D) = unitaryWeyl Q split j J hJ θ :=
    synchronizedWeylLifts_t Q split i j hij hVi hVj s μ₀ J hJ θ b hb c hc ξ k hk0 hAfull γ hCfull t
  refine ⟨g,θ,b,γ,ξ,d,hcover,hpanel,hb,rfl,hco,fun p => rfl,rfl,ht,?_⟩
  rw [ht]
  exact unitaryWeyl_source_factor Q split i j hij hVi hVj s μ₀ J hJ θ c hc ξ k hk0 hAfull γ hCfull t

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

/-- The genuine source presentation on the literal original quotient,
with exact coverage of the image of its original Sylow subgroup. -/
theorem original_native_data :
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)
      (d : UnitaryPresentation.FiveData Q split j (fiveForm J)),
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      d.roots = synchronizedRoots Q split i j hVi s μ₀ J b γ ξ ∧
      (Function.Injective (chartWord Q d.roots) ∧
        Set.range (chartWord Q d.roots) =
          ((S.subgroupOf (generated L S)).map Q.q : Set ((generated L S) ⧸ Q.D)) ∧
        d.roots.generated = (S.subgroupOf (generated L S)).map Q.q) ∧
      (∀ p, d.cartan p = GTwoSource.alignedTorus Q split i hVi μ₀ s (Units.map ξ.toMonoidHom p.1)*
        unitaryTorus Q split j J hJ θ (unitaryCartanParameter J p)) ∧
      d.lifts.s = s.val ∧
      (d.lifts.t : (generated L S) ⧸ Q.D) = unitaryWeyl Q split j J hJ θ ∧
      ∃ u : Eˣ, (t.val : (generated L S) ⧸ Q.D) = unitaryTorus Q split j J hJ θ u * d.lifts.t := by
  dsimp only
  obtain ⟨g,θ,b,γ,ξ,d,hcover,hpanel,hb,hr,hco,hH,hs,ht,hfactor⟩ :=
    marked_native_data Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,ξ,d,hcover,hpanel,hb,hr,?_,hH,hs,ht,hfactor⟩
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  exact hco

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
