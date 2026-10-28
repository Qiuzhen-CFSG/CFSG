module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.LinearNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.ReflectedApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.LinearAxes

/-!
# Original common labels for the two natural U₅ sections

The original linear epimorphism and full panel indices construct the actual
SL₂ Frattini-section coordinates. The two whole unitary roots occupy its
two axes, with their entire intrinsic centers as kernels and the full
quadratic coefficient field as image.

Combining this with the constructed SU₃ section and reflected whole-root
charts gives one additive equivalence from the SU₃ field to the SL₂ field,
with identical labels on B and D. The SU₃ covering map, projective panel
square, linear reflection and exact B–D crossing all remain attached to
these same roots. The original application evaluates both products and
linear actions on literal Q.q representatives, including q = 2 and q = 4.

This constructs the two natural sections used in the source comparison.
Multiplicativity of their common label, alignment with the derived-center
parameters, the remaining mixed/Cartan/Weyl equations and FiveData assembly
are still required for the full recognition theorem.
Source: Fong--Seitz II (8C), pp.203--204,206--208, (8.14)--(8.16), (8.32)--(8.33).
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


include e h hK hE hfixed hJ hm hij hVi hVj s hf hk ν hindexi hindexj

/-- Construct the linear natural section, its two root axes and their exact
full-center kernels, from the original profile and full panel indices. -/
theorem marked_linear_natural_section :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
    ∃ c : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
        ≃ₗ[ZMod 2] (Fin 2 → K),
      (∀ a v, c (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)
        (GTwoSource.alignedPinning Q split i hVi μ₀ s a) v) = Matrix.mulVec a.val (c v)) ∧
      (∀ v : simpleRemainder Q split i, (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) →
        (linearNaturalSectionMap Q split i c v).toAdd 1 = 0) ∧
      (∀ v : simpleRemainder Q split i, (v : X ⧸ Q.D) ∈ simpleRoot Q split j →
        (linearNaturalSectionMap Q split i c v).toAdd 0 = 0) ∧
      (linearCrossedCoordinate Q split i j hij c).ker = center (rootAt Q split j (Q.simple i)) ∧
      (linearSimpleCoordinate Q split i j hij c).ker = center (simpleRoot Q split j) ∧
      Function.Surjective (linearCrossedCoordinate Q split i j hij c) ∧
      Function.Surjective (linearSimpleCoordinate Q split i j hij c) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  dsimp only
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  let μ := (GTwoSource.alignedPinning Q split i hVi μ₀ s).symm
  obtain ⟨hA,hBj,hcardV,_,_⟩ := QuadrangleStructure.marked_unitary_root_orders Q e h split hm i j hij
    (2^n) (pow_pos (by decide) _) hindexi hindexj
  obtain ⟨c,hc⟩ := aligned_linear_frattini_coordinates Q split J n hK hE hfixed hJ hm i j hij
    hVi hVj s μ₀ ν hBj hcardV
  let a := GTwoSource.simpleRootFieldEquiv Q split i hVi μ₀
  let : IsElementaryAbelian 2 (Multiplicative K) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      change (2 : ℕ) • x.toAdd = 0
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero _) }
  have hAi := IsElementaryAbelian.of_surjective (p := 2) a.toMonoidHom a.surjective
  have hcomm := unitary_opposite_commutator Q split J (NeZero.pos n) hK hE hfixed hJ hm i j hij hVi hVj s μ ν
  have hcentral := linear_frattini_central Q split J (NeZero.pos n) hE hfixed hJ
    hm i j hij hVi hVj s ν hAi hA hcomm
  have hphi := (unitary_linear_derived_irreducible Q split J (NeZero.pos n) hK hE hfixed hJ
    hm i j hij hVi hVj s μ ν).1
  have hZ := (unitary_simpleRoot_special Q split J (NeZero.pos n) hE hfixed hJ j hVj ν).2
  have hker := linearCrossedCoordinate_ker Q split hm i j hij hVi hVj s μ₀ c hc hcentral hphi hZ
  have hz := simpleRoot_derived_center_card Q split j hVj J (NeZero.pos n) hE hfixed hJ ν
  have hZcard : Nat.card (center (simpleRoot Q split j)) = 2^n := by
    have hh := hz.2
    rw [hz.1,card_map_of_injective (simpleRoot Q split j).subtype_injective] at hh
    exact hh
  let eD := reflectedUnitaryChart Q split i j s (MulEquiv.refl (simpleRoot Q split j))
  have hZD : Nat.card (center (rootAt Q split j (Q.simple i))) = 2^n :=
    (Nat.card_congr (centerCongr eD).toEquiv).symm.trans hZcard
  have hD : Nat.card (rootAt Q split j (Q.simple i)) = (2^n)^3 := by
    simp only [rootAt,card_rightConjugate,hBj]
  have hsurj := linearCrossedCoordinate_surjective Q split i j hij c hK hD hZD hker
  exact ⟨c,hc,
    crossed_unitary_linear_axis Q split hm i j hij hVi hVj s μ₀ c hc,
    simple_unitary_linear_axis Q split hm i j hij hVi hVj s μ₀ c hc,hker,
    linearSimpleCoordinate_ker Q split i j hij hVi s μ₀ c hc hker,hsurj,
    linearSimpleCoordinate_surjective Q split i j hij hVi s μ₀ c hc hsurj⟩

include hconj t hπ hπν hQi hderived hfrattini

/-- The original SU₃ and SL₂ natural sections construct one common additive
label on both whole unitary roots, with the existing exact B–D equation. -/
theorem marked_common_natural_labels :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
      (c : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
        ≃ₗ[ZMod 2] (Fin 2 → K)) (ψ : E ≃+ K),
      let d := reflectedUnitaryChart Q split i j s b
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ a v, c (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)
        (GTwoSource.alignedPinning Q split i hVi μ₀ s a) v) = Matrix.mulVec a.val (c v)) ∧
      (∀ p : hermitianUnipotentCoord J,
        linearSimpleCoordinate Q split i j hij c (b p) = .ofAdd (ψ p.val.1) ∧
        linearCrossedCoordinate Q split i j hij c (d p) = .ofAdd (ψ p.val.1)) ∧
      (∀ a : E, (s.val : X ⧸ Q.D)*(γ (.ofAdd a) : X ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a))) ∧
      ∀ p q : hermitianUnipotentCoord J,
        (b p : X ⧸ Q.D)*(d q : X ⧸ Q.D) =
          (d q : X ⧸ Q.D)*(γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  dsimp only
  obtain ⟨g,θ,c₃,b,d,γ,hcover,hpanel,hc₃,hb,hd,hγ,hcross,_⟩ := marked_reflected_root_coordinates
    Q split e h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t f hf hk ν π hπ hπν
      hindexi hindexj hQi hderived hfrattini
  obtain ⟨c,hc,_,_,hker,_,hsurj,_⟩ := marked_linear_natural_section Q split e h J n hK hE hfixed hJ
    hm i j hij hVi hVj s f hf hk ν hindexi hindexj
  let μ₀ := UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk
  obtain ⟨ψ,hψ⟩ := linear_full_root_labels Q split i j hij hVi s μ₀ c hc J (NeZero.pos n) hE hfixed b hker hsurj
  have hde : d = reflectedUnitaryChart Q split i j s b := by
    apply MulEquiv.ext
    intro p
    apply Subtype.ext
    rw [hd,reflectedUnitaryChart_apply,inv_eq_of_mul_eq_one_right (GTwoSource.sourceReflection_sq Q split i hVi μ₀ s)]
  rw [hde] at hcross
  exact ⟨g,θ,b,γ,c,ψ,hcover,hpanel,hb,hc,hψ,hγ,hcross⟩

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

/-- Both full-root labels and the linear natural action are constructed on
the literal original quotient, retaining the SU₃ cover and projective square. -/
theorem original_common_natural_labels :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
      (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
      (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
      (c : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
        ≃ₗ[ZMod 2] (Fin 2 → K)) (ψ : E ≃+ K),
      let d := reflectedUnitaryChart Q split i j s b
      (∀ a, θ a = π (g*a*g⁻¹)) ∧
      (∀ a, ν (RootLocalCover.projection Q split j (θ a)) = J.specialToProjective (g*a*g⁻¹)) ∧
      (∀ p, (b p : (generated L S) ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p)) ∧
      (∀ p : hermitianUnipotentCoord J,
        linearSimpleCoordinate Q split i j hij c (b p) = .ofAdd (ψ p.val.1) ∧
        linearCrossedCoordinate Q split i j hij c (d p) = .ofAdd (ψ p.val.1)) ∧
      (∀ a : E, (s.val : (generated L S) ⧸ Q.D)*(γ (.ofAdd a) : (generated L S) ⧸ Q.D)*s.val =
        γ (.ofAdd (J.conj a))) ∧
      (∀ (p q : hermitianUnipotentCoord J) (B D : generated L S)
        (_hB : Q.q B = b p) (_hD : Q.q D = d q),
        Q.q (B*D) = Q.q D * (γ (.ofAdd (q.val.1*J.conj p.val.1)) : (generated L S) ⧸ Q.D) * Q.q B) ∧
      ∀ (a : SL(2,K)) (A V : generated L S)
        (_hA : Q.q A = GTwoSource.alignedPinning Q split i hVi μ₀ s a)
        (hV : Q.q V ∈ simpleRemainder Q split i),
        ∃ w : simpleRemainder Q split i,
          (w : (generated L S) ⧸ Q.D) = Q.q (A*V*A⁻¹) ∧
          c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) w)) =
            Matrix.mulVec a.val (c (.ofMul
              (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) ⟨Q.q V,hV⟩))) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  dsimp only
  obtain ⟨g,θ,b,γ,c,ψ,hcover,hpanel,hb,hc,hψ,hγ,hcross⟩ := marked_common_natural_labels
    Q split (originalMarkedIso Q) h J n hK hE hfixed hJ hconj hm i j hij hVi hVj s t
      f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  refine ⟨g,θ,b,γ,c,ψ,hcover,hpanel,hb,hψ,hγ,?_,?_⟩
  · intro p q B D hB hD
    rw [map_mul,hB,hD]
    exact hcross p q
  · intro a A V hA hV
    let μ₀ := UnitarySource.markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi f hf hk
    let w := remainderRankOneAction Q split i hVi
      (GTwoSource.alignedPinning Q split i hVi μ₀ s a) ⟨Q.q V,hV⟩
    refine ⟨w,?_,?_⟩
    · rw [remainderRankOneAction_apply,←hA,map_mul,map_mul,map_inv]
    · have hh := hc a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) ⟨Q.q V,hV⟩))
      change c (.ofMul (remainderFrattiniAction Q split i hVi
        (GTwoSource.alignedPinning Q split i hVi μ₀ s a)
          (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) ⟨Q.q V,hV⟩))) = _ at hh
      rw [remainderFrattiniAction_mk] at hh
      exact hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
