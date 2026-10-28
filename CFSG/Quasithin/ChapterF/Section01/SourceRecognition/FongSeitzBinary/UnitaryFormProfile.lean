module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFormTransport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFactorProfile

/-!
# The original unitary profile for an arbitrary Hermitian form

F.1.1 supplies an actual SU₃ or PSU₃ quotient for an arbitrary nondegenerate
Hermitian form. A single Hermitian basis change puts it in the antidiagonal
coordinates used by the proved U₅ profile. Transporting back preserves the
original special group, its scalar projection and the natural Frattini
representation. Both endpoint core preimages and all original-cover
representative equations are retained, including q=2.

The original linear quotient, quadratic field orders, special-core data and
marked split quadrangle are the only profile inputs. No Gram matrix, cover,
actor extension, Borel index or local regularity is an extra premise. This
discharges the coordinate-form premise of the existing profile theorem;
the original profile construction and the U₅ root equations remain with their
source owners, and exhaustive seven-row recognition remains unfinished.

Source: DGS (11.8), pp.175--176; Fong--Seitz I (6A)(c), pp.37--38,
II (8.13)--(8.15), pp.203--204; Huppert II.10.4(b).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
  (hK : Nat.card K = (2^n)^2)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
  (hQj : Nat.card ((parabolic L S j).pCoreIn 2) = (2^n)^7)
  (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
  (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2))
include mark h split hn hE hconj hK hm hij μi hfactor hQj hderived hfrattini

/-- The full original and root SU₃ comparisons, projective squares, scalar
kernel and natural coordinates require no chosen Gram matrix. -/
theorem marked_unitary_factor_coordinates_arbitrary_form :
    letI := MarkedLocal.originalRadicalInClosure_normal Q mark h split j
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ hr : ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
        pCore 2 (parabolic L S k),
    ∃ (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
      (ξ : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
      (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (γ : (MarkedLocal.originalLocalClosure Q mark split j ⧸
        MarkedLocal.originalRadicalInClosure Q mark split j) ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      Function.Surjective f ∧
      f.ker = (pCore 2 (parabolic L S i)).subgroupOf
        ((S ⊔ L i).subgroupOf (parabolic L S i)) ∧
      (∀ a : L i, f (MarkedLocal.originalFactorIntoActor i a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μi (QuotientGroup.mk' _ a))) ∧
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q mark h split j l) =
        J.specialToProjective (ξ l)) ∧
      (∀ r, ν (RootLocalCover.projection Q split j r) = J.specialToProjective (κ r)) ∧
      (RootLocalCover.projection Q split j).ker = center (rankOne Q split j) ∧
      (∀ l : L j, γ (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q mark h split j l)) =
        ξ (QuotientGroup.mk' (pCore 2 (L j)) l)) ∧
      (∀ r : MarkedLocal.originalRankOne Q mark split j,
        γ (QuotientGroup.mk' _ (inclusion (MarkedLocal.originalRankOne_le_localClosure Q mark split j) r)) =
          κ (MarkedLocal.originalRankOneEquiv Q mark split j r)) ∧
      ∀ r v, c (elementaryRepresentation (p := 2)
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainderFrattiniAction
          Q split j (hr j).1) r v) = Matrix.mulVec (κ r).val.val (c v) := by
  let := MarkedLocal.originalRadicalInClosure_normal Q mark h split j
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hE hfixed
  let a := specialEquiv J C hC
  let b := projectiveEquiv J C hC
  have hfactor' : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* (standardForm J).specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) := by
    rcases hfactor with ⟨⟨ξ⟩⟩ | ⟨⟨ν⟩⟩
    · exact Or.inl ⟨ξ.trans a⟩
    · exact Or.inr ⟨ν.trans b⟩
  obtain ⟨d,_,hfactors,_⟩ := marked_unitary_factor_profile Q mark h split (standardForm J)
    hn hE hconj hK rfl hm i j hij μi hfactor' hQj hderived hfrattini
  obtain ⟨hr,ξ,ν,κ,γ,c,hpanel,hfactorSquare,hker,hγl,hγr,hc⟩ :=
    UnitaryFiveSource.marked_unitary_profile_coordinates Q split mark h (standardForm J)
      hn hE rfl hconj hm i j hij hfactor' d.linear_index d.unitary_index
      d.linear_sylow_elementary hQj hderived hfrattini
  refine ⟨hr,d.linear_actor,ξ.trans a.symm,ν.trans b.symm,κ.trans a.symm,
    γ.trans a.symm,c.trans (UnitaryFormTransport.basisCoordinates C),
    d.linear_surjective,d.linear_kernel,hfactors,?_,?_,hker,?_,?_,?_⟩
  · intro l
    change b.symm (ν _) = J.specialToProjective (a.symm (ξ l))
    rw [hfactorSquare]
    exact UnitaryFormTransport.projective_symm_square J C hC _
  · intro r
    change b.symm (ν _) = J.specialToProjective (a.symm (κ r))
    rw [hpanel]
    exact UnitaryFormTransport.projective_symm_square J C hC _
  · intro l
    exact congrArg a.symm (hγl l)
  · intro r
    exact congrArg a.symm (hγr r)
  · intro r v
    change UnitaryFormTransport.basisCoordinates C (c _) =
      (a.symm (κ r)).val.val.mulVec (UnitaryFormTransport.basisCoordinates C (c v))
    rw [hc]
    exact UnitaryFormTransport.basisCoordinates_action J C hC (κ r) (c v)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
