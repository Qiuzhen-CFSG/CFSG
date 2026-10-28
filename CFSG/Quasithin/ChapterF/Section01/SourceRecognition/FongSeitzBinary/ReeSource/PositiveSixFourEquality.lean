module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.BinaryPerpendicular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OmegaNonzero

/-!
# The all-parameter (6.4) commutator fills the shifted Omega

The perpendicular Suzuki roots now commute. If (6.4) vanished, four
actual ordered root factors, of orders q, q, q and q^2, would embed in
the radical centralizer of the simple Suzuki root. Its order would be
at least q^5, contradicting the source (6.1) bound q^4. Cartan transitivity
then upgrades nonvanishing to equality with the shifted Omega.

Source: Fong--Seitz I (6H)(c), printed p.55. The natural panel markings,
odd linear degree and faithful Borel remain explicit. The binary case is
included; the remaining source construction is not inferred here.
OriginalPositivePerpendicular and Section10Perpendicular supply the literal original and Section 10 applications.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private theorem right_rep (k : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) =
      rootAt Q split k (v*w) := rootAt_right Q split k v w _ (representative_spec _)

private theorem five_list (hm : rotationOrder Q = 8) :
    orderedRoots Q split true 5 =
      [simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1),
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)] := by
  simp only [orderedRoots,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,List.map_cons,List.map_nil]
  change [simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1),
    rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 1) : X ⧸ Q.D),
    rightConjugate (rightConjugate (rootAt Q split 0 (Q.simple 1))
      (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D),
    rightConjugate (rightConjugate (rightConjugate (rootAt Q split 1 (Q.simple 0))
      (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D))
      (representative (Q.simple 1) : X ⧸ Q.D)] = _
  rw [right_rep,right_rep,right_rep,right_rep,right_rep]
  have he : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0*Q.simple 1) =
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
    rw [←right_rep]
    exact perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
  rw [he]

private theorem four_injective (hm : rotationOrder Q = 8) :
    Function.Injective (fun p : rootAt Q split 0 (Q.simple 1) ×
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) ×
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) ×
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =>
      (p.1 : X ⧸ Q.D)*p.2.1*p.2.2.1*p.2.2.2) := by
  have hinj : Function.Injective (rootProduct (orderedRoots Q split true 5)) := by
    intro p q he
    apply (orderedCoordinates Q split true 5 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [five_list Q split hm] at hinj
  intro p q he
  have hh := hinj
    (a₁ := (1,p.1,inclusion (omegaOneAmbient_le _) p.2.1,p.2.2.1,p.2.2.2,PUnit.unit))
    (a₂ := (1,q.1,inclusion (omegaOneAmbient_le _) q.2.1,q.2.2.1,q.2.2.2,PUnit.unit))
    (by simpa only [rootProduct,coe_one,coe_inclusion,one_mul,mul_one,mul_assoc] using he)
  refine Prod.ext (congrArg (fun z => z.2.1) hh) (Prod.ext ?_ ?_)
  · apply Subtype.ext
    exact congrArg (fun z => (z.2.2.1 : X ⧸ Q.D)) hh
  · exact Prod.ext (congrArg (fun z => z.2.2.2.1) hh) (congrArg (fun z => z.2.2.2.2.1) hh)

private theorem last_linear_le_remainder (hm : rotationOrder Q = 8) :
    rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) ≤ simpleRemainder Q split 1 := by
  have hs (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hi (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right (hs k)
  have h03 := wordLength_alternatingWord Q false (n := 3) (by omega)
  have h02 := wordLength_alternatingWord Q false (n := 2) (by omega)
  have h13 := wordLength_alternatingWord Q true (n := 3) (by omega)
  have h14 := wordLength_alternatingWord Q true (n := 4) (by omega)
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,mul_one,←mul_assoc] at h03 h02 h13 h14
  apply rootAt_le_remainder Q split 0 1 _ <;>
    simp only [mul_inv_rev,hi,←mul_assoc (Q.simple 1) (Q.simple 1),hs,
      one_mul,←mul_assoc,h03,h02,h13,h14]

include μ hB in
private theorem omega_card (w : Weyl Q) :
    Nat.card (omegaOneAmbient (rootAt Q split 1 w)) = 2^(2*m+1) := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map e.toMonoidHom = rootAt Q split 1 w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←he,←map_omegaOneAmbient_injective e.toMonoidHom e.injective,
    card_map_of_injective e.injective]
  exact suzukiOmega_card Q split 1 m μ hB

include ν hC μ hB hn in
/-- Perpendicular commutation and (6.1) force the (6.4) commutator for all parameters
to be the full shifted Omega. -/
theorem source_six_four_eq
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  have hcard : Nat.card (BinaryGaloisField n) = 2^(2*m+1) := by
    rw [GaloisField.card 2 n hn.pos.ne',ree_common_field_exponent Q split hm n hn m ν T hC μ hB
      (UnitarySource.actorReflection Q split) hcore]
  apply source_six_four_eq_of_nonzero Q split 1 0 m μ hB n hn.pos ν T hC hc hm (by decide)
    (by rw [hcard]; exact Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide))
  intro hzero
  let Z := simpleRemainder Q split 1 ⊓ centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D))
  let B := rootAt Q split 0 (Q.simple 1)
  let C := omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1))
  let D := rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  have hv := octagon_three_roots_le_remainder Q split hm 1 0 (by decide)
  have hBz : B ≤ Z := le_inf hv.1 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans (adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
      (marked_linear_remainder_le_kernel Q split 0 ν T hC))))
  have hCz : C ≤ Z := le_inf ((omegaOneAmbient_le _).trans hv.2.1)
    (commutator_eq_bot_iff_le_centralizer.mp (source_shifted_omega_commute Q split 1 0 m μ hB ν T hC hm (by decide)))
  have hDz : D ≤ Z := le_inf (last_linear_le_remainder Q split hm)
    (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hzero))
  have hEz : E ≤ Z := le_inf hv.2.2 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans (source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc)))
  let f : B × C × D × E → Z := fun p =>
    ⟨(p.1 : X ⧸ Q.D)*p.2.1*p.2.2.1*p.2.2.2,
      Z.mul_mem (Z.mul_mem (Z.mul_mem (hBz p.1.property) (hCz p.2.1.property)) (hDz p.2.2.1.property)) (hEz p.2.2.2.property)⟩
  have hlo := Nat.card_le_card_of_injective f (fun p q h => four_injective Q split hm (congrArg Subtype.val h))
  have hBcard : Nat.card B = 2^(2*m+1) := by
    rw [linear_rootAt_card Q split 0 n ν T hC hn.pos,
      ree_common_field_exponent Q split hm n hn m ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
  have hDcard : Nat.card D = 2^(2*m+1) := by
    rw [linear_rootAt_card Q split 0 n ν T hC hn.pos,
      ree_common_field_exponent Q split hm n hn m ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
  have hCcard : Nat.card C = 2^(2*m+1) := omega_card Q split m μ hB _
  have hEcard : Nat.card E = (2^(2*m+1))^2 := by
    change Nat.card (rightConjugate (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) = _
    rw [Nat.card_congr (RootAction.conjugateEquiv (simpleRoot Q split 1) (representative (Q.simple 0*Q.simple 1*Q.simple 0))).toEquiv,
      Nat.card_congr (suzukiRootEquiv Q split 1 m μ hB).toEquiv,matrixRoot_card]
  rw [Nat.card_prod,Nat.card_prod,Nat.card_prod,hBcard,hCcard,hDcard,hEcard] at hlo
  have hhi := (source_six_one Q split 1 0 ν T hC m μ hB hc hm (by decide) hcard.le).1
  rw [hcard] at hhi
  have hpow : (2^(2*m+1))^5 ≤ (2^(2*m+1))^4 := by
    calc
      _ = 2^(2*m+1)*(2^(2*m+1)*(2^(2*m+1)*(2^(2*m+1))^2)) := by ring
      _ ≤ _ := hlo.trans hhi
  exact (Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide : 4 < 5)).not_ge hpow

set_option linter.unusedVariables false in
include ν hC μ hB hn in
/-- The existing positive-parameter specialization of the full (6.4) equality. -/
theorem source_positive_six_four_eq
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  exact source_six_four_eq Q split n hn m ν T hC μ hB hm hcore hc

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
