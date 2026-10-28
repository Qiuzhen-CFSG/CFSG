module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicAbelian
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryCubicFixed

/-!
# Original unitary factors and the full cubic radical centralizer

The original PSL2 and SU3/PSU3 markings supply the fixed-root identities
and the actual radical-kernel containment. Unique root coordinates then
identify the whole cubic radical centralizer with the three conjugate
Frattini groups in Fong--Seitz I (6F), printed pp.46--47. The full Cartan
and the two opposite unitary Frattini groups normalize it. Its abelianness
then follows from the short-root bounds and genuine unitary center
irreducibility, with no additional source premise. Both endpoint
orientations, scalar conventions and degree one are retained, with the
full original Borel and both endpoint inclusion squares.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

private theorem original_unitary_radical_kernel
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    simpleRemainder Q split j ≤ localKernel Q j := by
  obtain ⟨_,hab⟩ := original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj
  obtain ⟨E,hEfield,hEfin,hEcard,⟨μ⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  have hE2 : 2 < Nat.card E := by
    rw [hEcard,hab]
    exact (by decide : 2 < 2^2).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 2 ≤ 2*b by omega))
  have hregular := marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i μ
  exact (hregular j).1

/-- The literal product and both normalizing groups needed for the
quadratic (6F) commutator argument, at the original marked boundary. -/
theorem original_linear_unitary_cubic_radical
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let Y := simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))
    (Y : Set (X ⧸ Q.D)) =
      (rootFrattiniAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootFrattiniAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) ∧
    Q.tits.B ⊓ Q.tits.N ≤ normalizer (Y : Set (X ⧸ Q.D)) ∧
    rootFrattiniAt Q split j 1 ⊔ rootFrattiniAt Q split j (Q.simple j) ≤
      normalizer (Y : Set (X ⧸ Q.D)) := by
  obtain ⟨_,hfixed⟩ := original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj
  have hfree := fun w => (hfixed w).1
  have hfix : ∀ w, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w :=
    fun w => (hfixed w).2.1
  have hKj := original_unitary_radical_kernel Q e h split hm i j hij ha hb hi hj
  exact ⟨unitary_cubic_radical_product Q split hm i j hij hfree hfix,
    unitary_cubic_radical_cartan_normalizes Q split j hKj,
    unitary_cubic_radical_frattini_normalizes Q split j hKj hfix⟩

/-- The entire original cubic radical centralizer is abelian, including
the binary special and projective unitary factors and both orientations. -/
theorem original_linear_unitary_cubic_radical_abelian
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    IsMulCommutative ↥(simpleRemainder Q split j ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
  obtain ⟨_,hfixed⟩ := original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj
  have hKj := original_unitary_radical_kernel Q e h split hm i j hij ha hb hi hj
  apply unitary_cubic_radical_abelian Q split hm i j hij hKj
    (fun w => (hfixed w).1) (fun w => (hfixed w).2.1) (fun w => (hfixed w).2.2)
  intro D hD hne hN
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x, J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      D = rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) := by
    obtain ⟨μj,_,_,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj j hKj hmodel.symm
    have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb hcard hconj
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
      (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
    let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    obtain ⟨ep⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2^b) hcard hf
    have hphi := (hfixed (Q.simple i*Q.simple j*Q.simple i)).2.2
    unfold rootFrattiniAt at hD ⊢
    rw [hphi] at hD ⊢
    exact QuadrangleStructure.rootAt_center_eq_of_torus_invariant Q split
      (QuadrangleStructure.unitary_sylow_center_irreducible J₀ hb hcard hf rfl)
      j (μj.trans ep) hKj _ D hD hne hN
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,ν⟩ | ⟨F,hF,hfin,J,hcard,hconj,ν⟩
  · exact applyModel J hcard hconj (Or.inl ν)
  · exact applyModel J hcard hconj (Or.inr ν)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
