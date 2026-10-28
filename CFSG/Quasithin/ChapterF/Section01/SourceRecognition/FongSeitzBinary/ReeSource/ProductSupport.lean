module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FrattiniSupport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.MixedBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.CommonField

/-!
# Two-root Frattini and derived support on the marked source octagon

The actual adjacent roots A=U₂^(s₁s₂) and B=U₁^(s₂s₁s₂) commute by
conjugating the short-interval theorem. The natural linear panel marking
makes every element of B square-trivial. The existing (6.3) and the new
Frattini product obstruction therefore show that every element of
Φ(U_s₂) ∩ AB lies in Ω₁(A)B and has square one. This includes the actual
derived radical, without assuming that it equals the Frattini subgroup.

The first estimates keep the field orders independent. The final theorem
uses common-field recognition to discharge the size inequality while
retaining its genuine odd-linear-degree premise. Both rank-one markings,
full quotient and original root placement remain fixed, including m=0.
OriginalProductSupport supplies the actual original endpoint application.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, the product
order-four obstruction before (6.4). The conjugated mixed-commutator
placement, removal of the remaining linear factor in (6.4), and the final
mixed-commutator equality remain subsequent source steps.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include μ hB ν hC in
theorem source_shifted_pair_commute (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    ⁅rootAt Q split i (Q.simple j*Q.simple i),
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥ := by
  let w := Q.simple j*Q.simple i
  let n := (representative w : X ⧸ Q.D)
  have hc := adjacent_commutator_eq_bot Q split hm i j hij
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)
    (marked_linear_remainder_le_kernel Q split j ν T hC)
  have ht := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A n) hc
  have hconj (A B : Subgroup (X ⧸ Q.D)) :
      rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  have hbot : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) n = ⊥ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
  rw [hconj,hbot] at ht
  change ⁅rootAt Q split i w,rightConjugate (rootAt Q split j (Q.simple i)) n⁆ = ⊥ at ht
  rw [rootAt_right Q split j (Q.simple i) w (representative w) (representative_spec w)] at ht
  simpa only [w,mul_assoc] using ht

include ν hC in
private theorem linear_rootAt_square (w : Weyl Q)
    (x : X ⧸ Q.D) (hx : x ∈ rootAt Q split j w) : x^2 = 1 := by
  let e : rootAt Q split j w ≃* Multiplicative F :=
    (RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)).trans
      (linearRootEquiv Q split j ν T hC)
  have hs : (⟨x,hx⟩ : rootAt Q split j w)^2 = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (e ⟨x,hx⟩).toAdd = 0
    rw [two_nsmul,CharTwo.add_self_eq_zero]
  exact congrArg Subtype.val hs

include μ hB ν hC in
/-- The whole two-root product used before (6.4) has exponent two in Φ(V),
under the independent-field degree bound. The two factors need not lie in Φ(V). -/
theorem source_frattini_product_support
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)
    (z : X ⧸ Q.D)
    (hz : z ∈ (frattiniRadicalSection Q split i
      (marked_suzuki_remainder_le_kernel Q split i m μ hB)).numerator)
    (hp : z ∈ (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D))) :
    z^2 = 1 ∧
      z ∈ (omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) : Set (X ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  apply frattini_product_support Q split i
    (marked_suzuki_remainder_le_kernel Q split i m μ hB) m μ hB hc hm j hij
    (source_six_three Q split i j m μ hB ν T hC hm hij).2 ?_ _
    (source_shifted_pair_commute Q split i j m μ hB ν T hC hm hij)
    (linear_rootAt_square Q split j ν T hC _) z hz hp
  simpa only [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] using hsize

include μ hB ν hC in
/-- In particular the two-root support estimate applies to the actual derived radical. -/
theorem source_derived_product_support
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)
    (z : X ⧸ Q.D)
    (hz : z ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆)
    (hp : z ∈ (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D))) :
    z^2 = 1 ∧
      z ∈ (omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) : Set (X ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  apply source_frattini_product_support Q split i j m μ hB ν T hC hc hm hij hsize z ?_ hp
  let V := simpleRemainder Q split i
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hd : ⁅V,V⁆ ≤ (frattini V).map V.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  exact hd hz

omit i j m μ hB ν T hC in
/-- Common-field recognition supplies the product bound, retaining the
preceding odd-linear-degree hypothesis. No field equality is assumed. -/
theorem source_frattini_product_support_of_odd_degree
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hcore : Q.tits.B.normalCore = ⊥)
    (z : X ⧸ Q.D)
    (hz : z ∈ (frattiniRadicalSection Q split 1
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)).numerator)
    (hp : z ∈ (rootAt Q split 1 (Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D))) :
    z^2 = 1 ∧
      z ∈ (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  apply source_frattini_product_support Q split 1 0 m μ hB ν T hC hc hm (by decide) ?_ z hz hp
  rw [show Nat.card (BinaryGaloisField n) = 2^n from GaloisField.card 2 n hn.pos.ne',he]
  exact Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide : 4 < 6)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
